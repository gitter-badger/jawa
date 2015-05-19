/*
Copyright (c) 2013-2014 Fengguo Wei & Sankardas Roy, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*/
package org.sireum.jawa.alir.dataFlowAnalysis

import org.sireum.alir._
import org.sireum.util._
import org.sireum.jawa.alir.controlFlowGraph._
import org.sireum.pilar.ast._
import org.sireum.pilar.symbol.ProcedureSymbolTable
import org.sireum.jawa.Center
import scala.util.control.Breaks._
import scala.collection.mutable.HashMap
import scala.collection.mutable.SynchronizedMap
import org.sireum.jawa.alir.Context
import org.sireum.jawa.util.MyTimer
import org.sireum.pilar.symbol.Symbol.pp2r
import org.sireum.jawa.JawaProcedure

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
trait InterProceduralMonotoneDataFlowAnalysisResult[LatticeElement] extends InterProceduralDataFlowAnalysisResult[LatticeElement] {
  def entrySet : ICFGNode => ISet[LatticeElement]
  def exitSet : ICFGNode => ISet[LatticeElement]
  def entries(n : ICFGNode, callerContext : Context, esl : EntrySetListener[LatticeElement])
}


trait InterProceduralMonotoneDataFlowAnalysisResultExtended[LatticeElement] extends InterProceduralMonotoneDataFlowAnalysisResult[LatticeElement] {
  def getEntrySetMap(): HashMap[ICFGNode, ISet[LatticeElement]]
  def merge(another: InterProceduralMonotoneDataFlowAnalysisResultExtended[LatticeElement]) = {
    this.getEntrySetMap ++= another.getEntrySetMap()
    this.getExtraInfo.merge(another.getExtraInfo)
    this
  }
  val extraInfo:ExtraInfo[LatticeElement] = new ExtraInfo[LatticeElement]
  def getExtraInfo = extraInfo
  def updateWorklist = extraInfo.getHoleNodes()
  def getInfluenceTo(gen:InterProceduralMonotonicFunction[LatticeElement], 
      kill:InterProceduralMonotonicFunction[LatticeElement], 
      callr: CallResolver[LatticeElement]) = extraInfo.getInfluenceTo(gen, kill, callr)
  def setInfluenceFrom(gen:InterProceduralMonotonicFunction[LatticeElement], 
      kill:InterProceduralMonotonicFunction[LatticeElement], 
      callr: CallResolver[LatticeElement]) = extraInfo.setInfluenceFrom(gen, kill, callr)     
}

class ExtraInfo[LatticeElement]{  // this represents component level pool
  private var holeNodes: MSet[ICFGNode] = msetEmpty
  private var staticFacts: MSet[LatticeElement] = msetEmpty
  private var sentIntentFacts: MMap[JawaProcedure, ISet[LatticeElement]] = mmapEmpty
       // Note: we do not store "sent intent" facts par se. Instead, we store tuples like (destinationComp, intentMappedFacts) 
       // in the "sentIntentFacts" map, where a JawaProcedure is one target of an intent. 
       // One intent can cause multiple entries (if multiple destinations) in the above map.
  private val rpcData = new RpcData[LatticeElement]
  def getHoleNodes(): ISet[ICFGNode] = holeNodes.toSet
  def getStaticFacts(): ISet[LatticeElement] = staticFacts.toSet
  def getIntentFacts:IMap[JawaProcedure, ISet[LatticeElement]] = sentIntentFacts.toMap
  def getRpcData = rpcData
  def merge(another:ExtraInfo[LatticeElement]) = {
    mergeStaticFacts(another) 
    mergeIntentFacts(another)
    mergeRpcData(another)
    this
  }
  def mergeStaticFacts(another:ExtraInfo[LatticeElement]) = {
    staticFacts ++= another.getStaticFacts() // note that we do not merge holeNodes across components
    this
  }
  def mergeIntentFacts(another:ExtraInfo[LatticeElement]) = {
    another.getIntentFacts.foreach{
          case (x, y) =>
            if(!sentIntentFacts.contains(x))
              sentIntentFacts(x) = y
            else
              if(!y.subsetOf(sentIntentFacts(x)))
                   sentIntentFacts(x) ++= y
    } 
    this
  }
  def mergeRpcData(another:ExtraInfo[LatticeElement]) = {
    this.rpcData.merge(another.rpcData)
    this
  }
  def diffStaticFacts(another:ExtraInfo[LatticeElement]): ISet[LatticeElement] = {
    var temp = staticFacts -- another.getStaticFacts()
    temp ++=(another.getStaticFacts() -- staticFacts)
    temp.toSet
  }
  def diffIntentFacts(another:ExtraInfo[LatticeElement]):IMap[JawaProcedure, ISet[LatticeElement]] = (sentIntentFacts.toSet diff another.getIntentFacts.toSet).toMap
  def hasLessStaticFactsThan(another:ExtraInfo[LatticeElement]) = {
    var status = false
    another.getStaticFacts().foreach { 
      x =>
        if(!staticFacts.contains(x))
        status = true
    }
    status
  }
  def hasLessIntentFactsThan(another:ExtraInfo[LatticeElement]) = {
    var status = false
    another.getIntentFacts.foreach{
            case (x, y) =>
              if(!sentIntentFacts.contains(x))
                status = true
              else
                if(!y.subsetOf(sentIntentFacts(x)))
                    status = true
    }
    status
  }
  def hasLessRpcFactsThan(another:ExtraInfo[LatticeElement]) = {
    getRpcData.hasLessFactsThan(another.getRpcData)
  }
  def findIntentDestComp(another:ExtraInfo[LatticeElement]) = {
    var dests: ISet[JawaProcedure] = Set()    
    another.getIntentFacts.foreach{
          case (x, y) =>
            if(!sentIntentFacts.contains(x))
              dests += x
            else
              if(!y.subsetOf(sentIntentFacts(x)))
                  dests += x 
    }
    dests
  }
  def getInfluenceTo(gen:InterProceduralMonotonicFunction[LatticeElement], 
      kill:InterProceduralMonotonicFunction[LatticeElement], 
      callr : CallResolver[LatticeElement]): Unit = {
    gen.setProperty("holeNodes", getHoleNodes())
    gen.setProperty("globalFacts", getStaticFacts())
    callr.setProperty("sentIntentFacts", getIntentFacts)
    callr.setProperty("rpcData", getRpcData)
  }  
  def setInfluenceFrom(gen:InterProceduralMonotonicFunction[LatticeElement], 
      kill:InterProceduralMonotonicFunction[LatticeElement], 
      callr : CallResolver[LatticeElement]): Unit = {
    holeNodes ++= gen.getPropertyOrElse("holeNodes", Set())
    staticFacts ++= gen.getPropertyOrElse("globalFacts", Set())
    sentIntentFacts ++= callr.getPropertyOrElse("sentIntentFacts", Map())
    rpcData.merge(callr.getPropertyOrElse("rpcData", new RpcData [LatticeElement]))
  }  
}

class RpcData [LatticeElement]{  // this represents caller-callee-facts for a RPC method
private var calleeCallers:MMap[JawaProcedure, Set[RpcCaller[LatticeElement]]] = mmapEmpty
def getCalleeCallers:Map[JawaProcedure, Set[RpcCaller[LatticeElement]]] = {
 calleeCallers.toMap 
}
def getCallersByCallee(callee: JawaProcedure):Set[RpcCaller[LatticeElement]] = {
  calleeCallers.getOrElse(callee, isetEmpty)
}
def init(callee: JawaProcedure, caller: RpcCaller [LatticeElement]) = {
  calleeCallers(callee)= Set(caller)
}
def add(callee: JawaProcedure, caller: RpcCaller [LatticeElement]) ={
  val temp = new RpcData[LatticeElement]
  temp.init(callee,caller)
  merge(temp)
  this
}
  def merge(another:RpcData[LatticeElement]) = {
    another.getCalleeCallers.keys.foreach { 
      callee =>
        if(calleeCallers.contains(callee)){
          val myCallers = calleeCallers(callee)
          val otherCallers = another.getCalleeCallers(callee)
          myCallers.map { 
            mc =>
              otherCallers.map { 
                oc => 
                  if(oc.equals(mc)) {
                    mc.callFacts ++=oc.callFacts
                    mc.retFacts ++=oc.retFacts
                  }
              }                  
          }
          val diffCallers = otherCallers.diff(myCallers)
          val totalCallers = myCallers ++ diffCallers
          calleeCallers.update(callee, totalCallers)
        }            
        else
          calleeCallers.update(callee, another.getCalleeCallers(callee))
    }
    this
  }
  def hasLessFactsThan(another:RpcData[LatticeElement]) = {
    var result = false
    another.getCalleeCallers.keys.foreach { 
    callee =>
      if(calleeCallers.contains(callee)){
        val myCallers = calleeCallers(callee)
        val otherCallers = another.getCalleeCallers(callee)
        myCallers.map { 
          mc =>
            otherCallers.map { 
              oc => 
                if(oc.equals(mc)) {
                  oc.callFacts.map { x => if(!mc.callFacts.contains(x)) result = true}
                  oc.retFacts.map { x => if(!mc.retFacts.contains(x)) result = true} 
                }
            }                  
        }
        val diffCallers = otherCallers.diff(myCallers)
        if(!diffCallers.isEmpty)
          result = true
      }            
      else
        result = true
    }
    result
  }
}
case class RpcCaller [LatticeElement](callerCallNode: ICFGCallNode, callerRetNode: ICFGReturnNode){
  var callFacts: MSet[LatticeElement] = msetEmpty[LatticeElement]
  var retFacts: MSet[LatticeElement] = msetEmpty[LatticeElement]
}

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
trait InterProceduralMonotonicFunction[LatticeElement] extends PropertyProvider {
   val propertyMap = mlinkedMapEmpty[Property.Key, Any]
	import org.sireum.pilar.ast._

  def apply(s : ISet[LatticeElement], a : Assignment, currentNode : ICFGLocNode) : ISet[LatticeElement]
  def apply(s : ISet[LatticeElement], e : Exp, currentNode : ICFGLocNode) : ISet[LatticeElement]
	def apply(s : ISet[LatticeElement], a : Action, currentNode : ICFGLocNode) : ISet[LatticeElement]
}

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
trait NodeListener {
  def onPreVisitNode(node : InterProceduralMonotoneDataFlowAnalysisFramework.N, preds : CSet[InterProceduralMonotoneDataFlowAnalysisFramework.N])
  def onPostVisitNode(node : InterProceduralMonotoneDataFlowAnalysisFramework.N, succs : CSet[InterProceduralMonotoneDataFlowAnalysisFramework.N])
}

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
trait CallResolver[LatticeElement] extends PropertyProvider{
  val propertyMap = mlinkedMapEmpty[Property.Key, Any]
  /**
	 * It returns the facts for each callee entry node and caller return node
	 */
  def resolveCall(s : ISet[LatticeElement], cj : CallJump, callerContext : Context, icfg : InterproceduralControlFlowGraph[ICFGNode]) : (IMap[ICFGNode, ISet[LatticeElement]], ISet[LatticeElement])
  def getAndMapFactsForCaller(calleeS : ISet[LatticeElement], callerNode : ICFGNode, calleeExitNode : ICFGVirtualNode) : ISet[LatticeElement]
}

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
object InterProceduralMonotoneDataFlowAnalysisFramework {
  
  final val TITLE = "InterProceduralMonotoneDataFlowAnalysisFramework"
  type N = ICFGNode
	def apply[LatticeElement] = build[LatticeElement] _

  def build[LatticeElement] //
  (icfg : InterproceduralControlFlowGraph[N], 
   forward : Boolean, lub : Boolean, rapid : Boolean, par : Boolean,
   gen : InterProceduralMonotonicFunction[LatticeElement],
   kill : InterProceduralMonotonicFunction[LatticeElement],
   callr : CallResolver[LatticeElement],
   iota : ISet[LatticeElement],
   initial : ISet[LatticeElement],
   timer : Option[MyTimer] = None,
   switchAsOrderedMatch : Boolean = false,
   nl : Option[NodeListener] = None) : //
   InterProceduralMonotoneDataFlowAnalysisResult[LatticeElement] = {

    val confluence = if (lub) iunion[LatticeElement] _ else iintersect[LatticeElement] _
    val bigConfluence : Iterable[ISet[LatticeElement]] => ISet[LatticeElement] =
      if (lub) bigIUnion else bigIIntersect

    val flow = if (forward) icfg else icfg.reverse
    val entrySetMap = if(par) new HashMap[N, ISet[LatticeElement]] with SynchronizedMap[N, ISet[LatticeElement]]
    									else new HashMap[N, ISet[LatticeElement]]
    
    def getEntrySet(n : N) = entrySetMap.getOrElse(n, initial)
    
    class IMdaf(val entrySet : N => ISet[LatticeElement],
               initial : ISet[LatticeElement])
        extends InterProceduralMonotoneDataFlowAnalysisResult[LatticeElement] {
      type DFF = ISet[LatticeElement]

      override def toString = {
        val sb = new StringBuilder
        var i = 1
        breakable{
	        for (n <- icfg.nodes) {
	          i += 1
	          if(i < 1000){
	          	sb.append("%s = %s\n".format(n, entrySet(n).toString))
	          } else break
	        }
        }
        sb.append("\n")

        sb.toString
      }
      
      def exitSet : N => DFF = {
	      _ match{
	        case en : ICFGEntryNode =>
	          getEntrySet(en)
	        case xn : ICFGExitNode =>
	          getEntrySet(xn)
	        case cn : ICFGCallNode =>
	          val r = caculateResult(cn)
	          r.map(_._2).reduce(iunion[LatticeElement])
	        case rn : ICFGReturnNode =>
	          getEntrySet(rn)
	        case nn : ICFGNormalNode =>
	          val r = caculateResult(nn)
	          r.map(_._2).reduce(iunion[LatticeElement])
	        case a => throw new RuntimeException("unexpected node type: " + a)
	      }
	    }

      
      protected def next(l : LocationDecl, pst : ProcedureSymbolTable, pSig : String, callerContext : Context) = {
        val newLoc = pst.location(l.index + 1)
        val newContext = callerContext.copy
        if(!newLoc.name.isDefined)
        	newContext.setContext(pSig, newLoc.index.toString)
        else 
          newContext.setContext(pSig, newLoc.name.get.uri)
        if(icfg.isCall(newLoc))
          icfg.getICFGCallNode(newContext)
        else
        	icfg.getICFGNormalNode(newContext)
      }

      protected def node(l : LocationDecl, context : Context) = {
        if(icfg.isCall(l))
          icfg.getICFGCallNode(context)
        else
        	icfg.getICFGNormalNode(context)
      }

      protected def fA(a : Assignment, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, a, currentNode).union(gen(in, a, currentNode))
        
      protected def fC(a : Action, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, a, currentNode).union(gen(in, a, currentNode))

      protected def fE(e : Exp, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, e, currentNode).union(gen(in, e, currentNode))

      protected def fOE(eOpt : Option[Exp], in : DFF, currentNode : ICFGLocNode) : DFF =
        if (eOpt.isDefined) fE(eOpt.get, in, currentNode) else in

      protected def actionF(in : DFF, a : Action, currentNode : ICFGLocNode) =
        a match {
          case a : AssignAction => fA(a, in, currentNode)
          case a : AssertAction => fC(a, in, currentNode)
          case a : AssumeAction => fC(a, in, currentNode)
          case a : ThrowAction  => fC(a, in, currentNode)
          case a : StartAction =>
            if (forward)
              fOE(a.arg, fOE(a.count, in, currentNode), currentNode)
            else
              fOE(a.count, fOE(a.arg, in, currentNode), currentNode)
          case a : ExtCallAction => fA(a, in, currentNode)
        }
      
      def update(s : DFF, n : N) : Boolean = {
        val oldS = getEntrySet(n)
        val newS = s
        if (oldS != newS) {
          entrySetMap.update(n, newS)
          true
        } else
          false
      }

      protected def visitBackward(
        currentNode : ICFGLocNode,
        esl : Option[EntrySetListener[LatticeElement]]) : IMap[N, DFF] = {
        val pst = Center.getProcedureWithoutFailing(currentNode.getOwner).getProcedureBody
        val l = pst.location(currentNode.getLocIndex)
        val currentContext = currentNode.getContext
        val callerContext = currentContext.copy.removeTopContext
        val pSig = pst.procedure.getValueAnnotation("signature") match {
            case Some(exp : NameExp) =>
              exp.name.name
            case _ => throw new RuntimeException("Doing " + TITLE + ": Can not find signature from: " + l)
          }
        
        val latticeMap : MMap[N, DFF] = mmapEmpty 
        
        if(!l.name.isDefined)
        	currentContext.setContext(pSig, l.index.toString)
        else
          currentContext.setContext(pSig, l.name.get.uri)
        val eslb = esl.getOrElse(null)
          def jumpF(j : Jump) : DFF =
            j match {
              case j : IfJump =>
                var result = initial
                val numOfIfThens = j.ifThens.size
                for (i <- 0 until numOfIfThens) {
                  val ifThen = j.ifThens(i)
                  val ifThenContext = callerContext.copy
                  ifThenContext.setContext(pSig, ifThen.target.uri)
                  val ifThenLoc = pst.location(ifThen.target.uri)
                  val sn = node(ifThenLoc, ifThenContext)
                  var r = getEntrySet(sn)
                  for (k <- tozero(i)) {
                    val it = j.ifThens(k)
                    r = fE(it.cond, r, currentNode)
                  }
                  result = confluence(result, r)
                }
                {
                  val ifElse = j.ifElse
                  val ifElseDefined = ifElse.isDefined
                  val sn =
                    if (ifElseDefined) {
                      val ifElseContext = callerContext.copy
		                  ifElseContext.setContext(pSig, ifElse.get.target.uri)
		                  val ifElseLoc = pst.location(ifElse.get.target.uri)
                      node(ifElseLoc, ifElseContext)
                    }
                    else next(l, pst, pSig, callerContext)
                  var r = getEntrySet(sn)
                  for (k <- tozero(numOfIfThens - 1)) {
                    val it = j.ifThens(k)
                    r = fE(it.cond, r, currentNode)
                  }
                  if (ifElseDefined && esl.isDefined) eslb.ifElse(ifElse.get, r)
                  result = confluence(result, r)
                }
                if (esl.isDefined) eslb.ifJump(j, result)
                result
              case j : SwitchJump =>
                var result = initial
                val numOfCases = j.cases.size
                for (i <- 0 until numOfCases) {
                  val switchCase = j.cases(i)
                  val switchCaseContext = callerContext.copy
                  switchCaseContext.setContext(pSig, switchCase.target.uri)
                  val switchCaseLoc = pst.location(switchCase.target.uri)
                  val sn = node(switchCaseLoc, switchCaseContext)
                  var r = getEntrySet(sn)
                  if (switchAsOrderedMatch)
                    for (k <- tozero(i)) {
                      val sc = j.cases(k)
                      r = fE(sc.cond, r, currentNode)
                    }
                  else
                    r = fE(switchCase.cond, r, currentNode)
                  if (esl.isDefined) eslb.switchCase(switchCase, r)
                  result = confluence(result, r)
                }
                {
                  val switchDefault = j.defaultCase
                  val switchDefaultDefined = switchDefault.isDefined
                  val sn =
                    if (switchDefaultDefined){
                      val switchDefaultContext = callerContext.copy
		                  switchDefaultContext.setContext(pSig, switchDefault.get.target.uri)
		                  val switchDefaultLoc = pst.location(switchDefault.get.target.uri)
                      node(switchDefaultLoc, switchDefaultContext)
                    }
                    else next(l, pst, pSig, callerContext)
                  var r = getEntrySet(sn)
                  if (switchAsOrderedMatch)
                    for (k <- tozero(numOfCases - 1)) {
                      val sc = j.cases(k)
                      r = fE(sc.cond, r, currentNode)
                    }
                  if (esl.isDefined && switchDefaultDefined)
                    eslb.switchDefault(switchDefault.get, r)
                  result = confluence(result, r)
                }
                if (esl.isDefined)
                  eslb.switchJump(j, result)
                result
              case j : GotoJump =>
                val jContext = callerContext.copy
                jContext.setContext(pSig, j.target.uri)
                val jLoc = pst.location(j.target.uri)
                val sn = node(jLoc, jContext)
                val result = getEntrySet(sn)
                if (esl.isDefined)
                  eslb.gotoJump(j, result)
                result
              case j : ReturnJump =>
                val exitContext = callerContext.copy
                exitContext.setContext(pSig, pSig)
                val sn = icfg.getICFGExitNode(exitContext)
                val result = fOE(j.exp, getEntrySet(sn), currentNode)
                if (esl.isDefined)
                  eslb.returnJump(j, result)
                result
              case j : CallJump =>
                val s =
                  if (j.jump.isEmpty)
                    getEntrySet(next(l, pst, pSig, callerContext))
                  else
                    jumpF(j.jump.get)
                val result = fA(j, s, currentNode)
                if (esl.isDefined)
                  eslb.callJump(j, result)
                result
            }
        val ln = node(l, currentContext)
        l match {
          case l : ComplexLocation =>
            val result = bigConfluence(l.transformations.map { t =>
              var r =
                if (t.jump.isEmpty)
                  getEntrySet(next(l, pst, pSig, callerContext))
                else
                  jumpF(t.jump.get)
              val numOfActions = t.actions.size
              for (i <- untilzero(numOfActions)) {
                val a = t.actions(i)
                r = actionF(r, a, currentNode)
                if (esl.isDefined) eslb.action(a, r)
              }
              if (esl.isDefined) eslb.exitSet(None, r)
              r
            })
            latticeMap += (ln -> result)
          case l : ActionLocation =>
            val result = actionF(getEntrySet(next(l, pst, pSig, callerContext)), l.action, currentNode)
            if (esl.isDefined) {
              eslb.action(l.action, result)
              eslb.exitSet(None, result)
            }
            latticeMap += (ln -> result)
          case l : JumpLocation =>
            val result = jumpF(l.jump)
            if (esl.isDefined) {
              eslb.exitSet(None, result)
            }
            latticeMap += (ln -> result)
          case l : EmptyLocation =>
            val result = getEntrySet(next(l, pst, pSig, callerContext))
            if (esl.isDefined) {
              eslb.exitSet(None, result)
            }
            latticeMap += (ln -> result)
        }
        latticeMap.toMap
      }
      

      protected def visitForward(
        currentNode : ICFGLocNode,
        esl : Option[EntrySetListener[LatticeElement]]) : IMap[N, DFF] = {
        val pst = Center.getProcedureWithoutFailing(currentNode.getOwner).getProcedureBody
        val l = pst.location(currentNode.getLocIndex)
        val currentContext = currentNode.getContext
        val callerContext = currentContext.copy.removeTopContext
        val pSig = pst.procedure.getValueAnnotation("signature") match {
			      case Some(exp : NameExp) =>
			        exp.name.name
			      case _ => throw new RuntimeException("Doing " + TITLE + ": Can not find signature from: " + l)
			    }

        val latticeMap : MMap[N, DFF] = mmapEmpty 

        val eslb = esl.getOrElse(null)
        def jumpF(s : DFF, j : Jump) : Unit =
          j match {
            case j : IfJump =>
              var r = s
              if (esl.isDefined) eslb.ifJump(j, s)
              for (ifThen <- j.ifThens) {
                r = fE(ifThen.cond, r, currentNode)
                val ifThenContext = callerContext.copy
                ifThenContext.setContext(pSig, ifThen.target.uri)
                val ifThenLoc = pst.location(ifThen.target.uri)
                val sn = node(ifThenLoc, ifThenContext)
                if (esl.isDefined) {
                  eslb.ifThen(ifThen, r)
                  eslb.exitSet(Some(ifThen), r)
                }
                latticeMap += (sn -> r)
              }
              if (j.ifElse.isEmpty) {
                val sn = next(l, pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              } else {
                val ifElse = j.ifElse.get
                val ifElseContext = callerContext.copy
                ifElseContext.setContext(pSig, ifElse.target.uri)
                val ifElseLoc = pst.location(ifElse.target.uri)
                val sn = node(ifElseLoc, ifElseContext)
                if (esl.isDefined) {
                  eslb.ifElse(ifElse, r)
                  eslb.exitSet(Some(ifElse), r)
                }
                latticeMap += (sn -> r)
              }
            case j : SwitchJump =>
              var r = s
              if (esl.isDefined) eslb.switchJump(j, s)
              for (switchCase <- j.cases) {
                r =
                  if (switchAsOrderedMatch)
                    fE(switchCase.cond, r, currentNode)
                  else
                    fE(switchCase.cond, s, currentNode)
                val switchCaseContext = callerContext.copy
                switchCaseContext.setContext(pSig, switchCase.target.uri)
                val switchCaseLoc = pst.location(switchCase.target.uri)
                val sn = node(switchCaseLoc, switchCaseContext)
                if (esl.isDefined) {
                  eslb.switchCase(switchCase, r)
                  eslb.exitSet(Some(switchCase), r)
                }
                latticeMap += (sn -> r)
              }
              if (j.defaultCase.isEmpty) {
                val sn = next(l,pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              } else {
                val switchDefault = j.defaultCase.get
                val switchDefaultContext = callerContext.copy
                switchDefaultContext.setContext(pSig, switchDefault.target.uri)
                val switchDefaultLoc = pst.location(switchDefault.target.uri)
                val sn = node(switchDefaultLoc, switchDefaultContext)
                if (esl.isDefined) {
                  eslb.switchDefault(switchDefault, r)
                  eslb.exitSet(Some(switchDefault), r)
                }
                latticeMap += (sn -> r)
              }
            case j : GotoJump =>
              val gotoContext = callerContext.copy
              gotoContext.setContext(pSig, j.target.uri)
              val gotoLoc = pst.location(j.target.uri)
              val sn = node(gotoLoc, gotoContext)
              if (esl.isDefined) {
                eslb.gotoJump(j, s)
                eslb.exitSet(Some(j), s)
              }
              latticeMap += (sn -> s)
            case j : ReturnJump =>
              val exitContext = callerContext.copy
              exitContext.setContext(pSig, "Exit")
              val sn = icfg.getICFGExitNode(exitContext)
              val r = fOE(j.exp, s, currentNode)
              if (esl.isDefined) {
                eslb.returnJump(j, r)
                eslb.exitSet(Some(j), r)
              }
              latticeMap += (sn -> r)
            case j : CallJump =>
              if (esl.isDefined) eslb.callJump(j, s)
              val r = fA(j, s, currentNode)
              if (j.jump.isEmpty) {
                val (calleeFactsMap, retFacts) = callr.resolveCall(r, j, currentContext, icfg)
                calleeFactsMap.foreach{
                  case (calleeNode, calleeFacts) =>
		                latticeMap += (calleeNode -> calleeFacts)
                }
                val rn = icfg.getICFGReturnNode(currentContext)
                latticeMap += (rn -> retFacts)
                if (esl.isDefined) eslb.exitSet(None, getEntrySet(rn))
              } else
                jumpF(r, j.jump.get)
        }
        
        var s = getEntrySet(currentNode)
        l match {
          case l : ComplexLocation =>
            l.transformations.foreach { t =>
              var r = s
              t.actions.foreach { a =>
                if (esl.isDefined) eslb.action(a, r)
                r = actionF(r, a, currentNode)
              }
              if (t.jump.isDefined)
                jumpF(r, t.jump.get)
              else {
                val sn = next(l, pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              }
            }
          case l : ActionLocation =>
             if(esl.isDefined) eslb.action(l.action, s)
             val r = actionF(s, l.action, currentNode)
             if(esl.isDefined) eslb.exitSet(None, r)
             val node = icfg.getICFGNormalNode(currentContext)
             val succs = icfg.successors(node)
             succs.foreach(succ=>latticeMap += (succ -> r))
          case l : JumpLocation =>
            jumpF(s, l.jump)
          case l : EmptyLocation =>
            if (esl.isDefined)
              eslb.exitSet(None, s)
            val sn = next(l, pst, pSig, callerContext)
            latticeMap += (sn -> s)
        }
        latticeMap.toMap
      }
      
      def caculateResult(currentNode : ICFGLocNode,
                esl : Option[EntrySetListener[LatticeElement]] = None) : IMap[N, DFF] = {
        if (forward) visitForward(currentNode, esl)
        else visitBackward(currentNode, esl)
      }

      def visit(currentNode : ICFGLocNode,
                esl : Option[EntrySetListener[LatticeElement]] = None) : Boolean = {
        caculateResult(currentNode, esl).map{case (n, facts) => update(confluence(facts, getEntrySet(n)), n)}.exists(_ == true)
      }

      
      def entries(n : N, callerContext : Context, esl : EntrySetListener[LatticeElement]) = {
        n match {
          case cn : ICFGLocNode  =>
            visit(cn, Some(esl))
          case _ =>
        }
      }

    }
    
    val imdaf = new IMdaf(getEntrySet _, initial)
    
    def process(n : N) : ISet[N] = {
	    var result = isetEmpty[N]
	    n match {
	      case en : ICFGEntryNode =>
	        for (succ <- icfg.successors(n)) {
	          if(imdaf.update(getEntrySet(en), succ)){
	            result += succ
	          }
	        }
	      case xn : ICFGExitNode =>
	        for (succ <- icfg.successors(n)){
	          val factsForCaller = callr.getAndMapFactsForCaller(getEntrySet(xn), succ, xn)
	          imdaf.update(confluence(getEntrySet(succ), factsForCaller), succ)
	          result += succ
	        }
	      case cn : ICFGCallNode =>
	        if (imdaf.visit(cn)){
	          result ++= icfg.successors(n)
	        }
	      case rn : ICFGReturnNode =>
	        for (succ <- icfg.successors(n)) {
	          if(imdaf.update(getEntrySet(n), succ)){
	            result += succ
	          }
	        }
	      case nn : ICFGNormalNode =>
	        if (imdaf.visit(nn)){
	          result ++= icfg.successors(n)
	        }
	      case a => throw new RuntimeException("unexpected node type: " + a)
	    }
	    result
	  }
    
    entrySetMap.put(flow.entryNode, iota)
    val workList = mlistEmpty[N]
    workList += flow.entryNode
    while(!workList.isEmpty){
	    while (!workList.isEmpty) {
        if(timer.isDefined) timer.get.ifTimeoutThrow
	      if(false){
	        val newworkList = workList.par.map{
	          n =>
	            if(nl.isDefined) nl.get.onPreVisitNode(n, icfg.predecessors(n))
				      val newnodes = process(n)
				      if(nl.isDefined) nl.get.onPostVisitNode(n, icfg.successors(n))
				      newnodes
	        }.reduce(iunion[N])
	        workList.clear
	        workList ++= newworkList
	      } else {
		      val n = workList.remove(0)
		      if(nl.isDefined) nl.get.onPreVisitNode(n, icfg.predecessors(n))
		      workList ++= process(n)
		      if(nl.isDefined) nl.get.onPostVisitNode(n, icfg.successors(n))
	      }
	    }
	    val nodes = if(false) icfg.nodes.par else icfg.nodes
	    workList ++= nodes.map{
	      node =>
	        var newnodes = isetEmpty[N]
	        node match{
	          case xn : ICFGExitNode =>
	            if(nl.isDefined) nl.get.onPreVisitNode(xn, icfg.predecessors(xn))
	            val succs = icfg.successors(xn)
		          for (succ <- succs){
		            val factsForCaller = callr.getAndMapFactsForCaller(getEntrySet(xn), succ, xn)
		            if (imdaf.update(confluence(getEntrySet(succ), factsForCaller), succ))
		            	newnodes += succ
		          }
	            if(nl.isDefined) nl.get.onPostVisitNode(xn, succs)
	          case _ =>
	        }
	        newnodes
	    }.reduce(iunion[N])
    }
    imdaf
    
	}
}

object InterProceduralMonotoneDataFlowAnalysisFrameworkExtended {
  
  final val TITLE = "InterProceduralMonotoneDataFlowAnalysisFrameworkExtended"
  type N = ICFGNode
  def apply[LatticeElement] = build[LatticeElement] _

  def build[LatticeElement] //
  (cg : InterproceduralControlFlowGraph[N], 
   existingResult : InterProceduralMonotoneDataFlowAnalysisResultExtended[LatticeElement],
   forward : Boolean, lub : Boolean, rapid : Boolean, par : Boolean,
   gen : InterProceduralMonotonicFunction[LatticeElement],
   kill : InterProceduralMonotonicFunction[LatticeElement],
   callr : CallResolver[LatticeElement],
   iota : ISet[LatticeElement],
   initial : ISet[LatticeElement],
   switchAsOrderedMatch : Boolean = false,
   nl : Option[NodeListener] = None) : //
   InterProceduralMonotoneDataFlowAnalysisResultExtended[LatticeElement] = {

    val confluence = if (lub) iunion[LatticeElement] _ else iintersect[LatticeElement] _
    val bigConfluence : Iterable[ISet[LatticeElement]] => ISet[LatticeElement] =
      if (lub) bigIUnion else bigIIntersect

    val flow = if (forward) cg else cg.reverse
    val entrySetMap = if(existingResult!=null) 
                          existingResult.getEntrySetMap() 
                      else 
                          {if(par) new HashMap[N, ISet[LatticeElement]] with SynchronizedMap[N, ISet[LatticeElement]]
                             else new HashMap[N, ISet[LatticeElement]]
                          }
    
    def getEntrySet(n : N) = entrySetMap.getOrElse(n, initial)
    
    class IMdaf(val entrySet : N => ISet[LatticeElement],
               initial : ISet[LatticeElement])
        extends InterProceduralMonotoneDataFlowAnalysisResultExtended[LatticeElement] {
      type DFF = ISet[LatticeElement]

      override def getEntrySetMap = entrySetMap
      
      
      override def toString = {
        val sb = new StringBuilder
        var i = 1
        breakable{
          for (n <- cg.nodes) {
            i += 1
            if(i < 1000){
              sb.append("%s = %s\n".format(n, entrySet(n).toString))
            } else break
          }
        }
        sb.append("\n")

        sb.toString
      }
      
      def exitSet : N => DFF = {
        _ match{
          case en : ICFGEntryNode =>
            getEntrySet(en)
          case xn : ICFGExitNode =>
            getEntrySet(xn)
          case cn : ICFGCallNode =>
            val r = caculateResult(cn)
            r.map(_._2).reduce(iunion[LatticeElement])
          case rn : ICFGReturnNode =>
            getEntrySet(rn)
          case nn : ICFGNormalNode =>
            val r = caculateResult(nn)
            r.map(_._2).reduce(iunion[LatticeElement])
          case a => throw new RuntimeException("unexpected node type: " + a)
        }
      }

      
      protected def next(l : LocationDecl, pst : ProcedureSymbolTable, pSig : String, callerContext : Context) = {
        val newLoc = pst.location(l.index + 1)
        val newContext = callerContext.copy
        if(!newLoc.name.isDefined)
          newContext.setContext(pSig, newLoc.index.toString)
        else 
          newContext.setContext(pSig, newLoc.name.get.uri)
        if(cg.isCall(newLoc))
          cg.getICFGCallNode(newContext)
        else
          cg.getICFGNormalNode(newContext)
      }

      protected def node(l : LocationDecl, context : Context) = {
        if(cg.isCall(l))
          cg.getICFGCallNode(context)
        else
          cg.getICFGNormalNode(context)
      }

      protected def fA(a : Assignment, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, a, currentNode).union(gen(in, a, currentNode))
        
      protected def fC(a : Action, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, a, currentNode).union(gen(in, a, currentNode))

      protected def fE(e : Exp, in : DFF, currentNode : ICFGLocNode) : DFF =
        kill(in, e, currentNode).union(gen(in, e, currentNode))

      protected def fOE(eOpt : Option[Exp], in : DFF, currentNode : ICFGLocNode) : DFF =
        if (eOpt.isDefined) fE(eOpt.get, in, currentNode) else in

      protected def actionF(in : DFF, a : Action, currentNode : ICFGLocNode) =
        a match {
          case a : AssignAction => fA(a, in, currentNode)
          case a : AssertAction => fC(a, in, currentNode)
          case a : AssumeAction => fC(a, in, currentNode)
          case a : ThrowAction  => fC(a, in, currentNode)
          case a : StartAction =>
            if (forward)
              fOE(a.arg, fOE(a.count, in, currentNode), currentNode)
            else
              fOE(a.count, fOE(a.arg, in, currentNode), currentNode)
          case a : ExtCallAction => fA(a, in, currentNode)
        }
      
      def update(s : DFF, n : N) : Boolean = {
        val oldS = getEntrySet(n)
        val newS = s
        if (oldS != newS) {
          entrySetMap.update(n, newS)
          true
        } else
          false
      }



      protected def visitForward(
        currentNode : ICFGLocNode,
        esl : Option[EntrySetListener[LatticeElement]]) : IMap[N, DFF] = {
        val pst = Center.getProcedureWithoutFailing(currentNode.getOwner).getProcedureBody
        val l = pst.location(currentNode.getLocIndex)
        val currentContext = currentNode.getContext
        val callerContext = currentContext.copy.removeTopContext
        val pSig = pst.procedure.getValueAnnotation("signature") match {
            case Some(exp : NameExp) =>
              exp.name.name
            case _ => throw new RuntimeException("Doing " + TITLE + ": Can not find signature from: " + l)
          }

        var latticeMap : IMap[N, DFF] = imapEmpty 

        val eslb = esl.getOrElse(null)
        def jumpF(s : DFF, j : Jump) : Unit =
          j match {
            case j : IfJump =>
              var r = s
              if (esl.isDefined) eslb.ifJump(j, s)
              for (ifThen <- j.ifThens) {
                r = fE(ifThen.cond, r, currentNode)
                val ifThenContext = callerContext.copy
                ifThenContext.setContext(pSig, ifThen.target.uri)
                val ifThenLoc = pst.location(ifThen.target.uri)
                val sn = node(ifThenLoc, ifThenContext)
                if (esl.isDefined) {
                  eslb.ifThen(ifThen, r)
                  eslb.exitSet(Some(ifThen), r)
                }
                latticeMap += (sn -> r)
              }
              if (j.ifElse.isEmpty) {
                val sn = next(l, pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              } else {
                val ifElse = j.ifElse.get
                val ifElseContext = callerContext.copy
                ifElseContext.setContext(pSig, ifElse.target.uri)
                val ifElseLoc = pst.location(ifElse.target.uri)
                val sn = node(ifElseLoc, ifElseContext)
                if (esl.isDefined) {
                  eslb.ifElse(ifElse, r)
                  eslb.exitSet(Some(ifElse), r)
                }
                latticeMap += (sn -> r)
              }
            case j : SwitchJump =>
              var r = s
              if (esl.isDefined) eslb.switchJump(j, s)
              for (switchCase <- j.cases) {
                r =
                  if (switchAsOrderedMatch)
                    fE(switchCase.cond, r, currentNode)
                  else
                    fE(switchCase.cond, s, currentNode)
                val switchCaseContext = callerContext.copy
                switchCaseContext.setContext(pSig, switchCase.target.uri)
                val switchCaseLoc = pst.location(switchCase.target.uri)
                val sn = node(switchCaseLoc, switchCaseContext)
                if (esl.isDefined) {
                  eslb.switchCase(switchCase, r)
                  eslb.exitSet(Some(switchCase), r)
                }
                latticeMap += (sn -> r)
              }
              if (j.defaultCase.isEmpty) {
                val sn = next(l,pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              } else {
                val switchDefault = j.defaultCase.get
                val switchDefaultContext = callerContext.copy
                switchDefaultContext.setContext(pSig, switchDefault.target.uri)
                val switchDefaultLoc = pst.location(switchDefault.target.uri)
                val sn = node(switchDefaultLoc, switchDefaultContext)
                if (esl.isDefined) {
                  eslb.switchDefault(switchDefault, r)
                  eslb.exitSet(Some(switchDefault), r)
                }
                latticeMap += (sn -> r)
              }
            case j : GotoJump =>
              val gotoContext = callerContext.copy
              gotoContext.setContext(pSig, j.target.uri)
              val gotoLoc = pst.location(j.target.uri)
              val sn = node(gotoLoc, gotoContext)
              if (esl.isDefined) {
                eslb.gotoJump(j, s)
                eslb.exitSet(Some(j), s)
              }
              latticeMap += (sn -> s)
            case j : ReturnJump =>
              val exitContext = callerContext.copy
              exitContext.setContext(pSig, "Exit")
              val sn = cg.getICFGExitNode(exitContext)
              val r = if (j.exp.isEmpty) s else fE(j.exp.get, s, currentNode)
              if (esl.isDefined) {
                eslb.returnJump(j, r)
                eslb.exitSet(Some(j), r)
              }
              latticeMap += (sn -> r)
            case j : CallJump =>
              if (esl.isDefined) eslb.callJump(j, s)
              val r = fA(j, s, currentNode)
              if (j.jump.isEmpty) {
                val (calleeFactsMap, retFacts) = callr.resolveCall(r, j, currentContext, cg)
                calleeFactsMap.foreach{
                  case (calleeNode, calleeFacts) =>
                    latticeMap += (calleeNode -> calleeFacts)
                }
                val rn = cg.getICFGReturnNode(currentContext)
                latticeMap += (rn -> retFacts)
                if (esl.isDefined) eslb.exitSet(None, getEntrySet(rn))
              } else
                jumpF(r, j.jump.get)
        }
        
        var s = getEntrySet(currentNode)
        l match {
          case l : ComplexLocation =>
            l.transformations.foreach { t =>
              var r = s
              t.actions.foreach { a =>
                if (esl.isDefined) eslb.action(a, r)
                r = actionF(r, a, currentNode)
              }
              if (t.jump.isDefined)
                jumpF(r, t.jump.get)
              else {
                val sn = next(l, pst, pSig, callerContext)
                if (esl.isDefined) eslb.exitSet(None, r)
                latticeMap += (sn -> r)
              }
            }
          case l : ActionLocation =>
             if(esl.isDefined) eslb.action(l.action, s)
             val r = actionF(s, l.action, currentNode)
             
             if(esl.isDefined) eslb.exitSet(None, r)
             val node = cg.getICFGNormalNode(currentContext)
             val succs = cg.successors(node)
             succs.foreach(succ=>latticeMap += (succ -> r))
          case l : JumpLocation =>
            jumpF(s, l.jump)
          case l : EmptyLocation =>
            if (esl.isDefined)
              eslb.exitSet(None, s)
            val sn = next(l, pst, pSig, callerContext)
            latticeMap += (sn -> s)
        }
        latticeMap
      }
      
      def caculateResult(currentNode : ICFGLocNode,
                esl : Option[EntrySetListener[LatticeElement]] = None) : IMap[N, DFF] = {
//        if (forward) visitForward(l, esl)
//        else visitBackward(l, esl)
        visitForward(currentNode, esl)
      }

      def visit(currentNode : ICFGLocNode,
                esl : Option[EntrySetListener[LatticeElement]] = None) : Boolean = {
        caculateResult(currentNode, esl).map{case (n, facts) => update(confluence(facts, getEntrySet(n)), n)}.exists(_ == true)
      }

      
      def entries(n : N, callerContext : Context, esl : EntrySetListener[LatticeElement]) = {
        n match {
          case cn : ICFGLocNode  =>
            visit(cn, Some(esl))
          case _ =>
        }
      }

    }
    
    val imdaf = new IMdaf(getEntrySet _, initial)
    
    def process(n : N) : ISet[N] = {
      var result = isetEmpty[N]
      n match {
        case en : ICFGEntryNode =>
          for (succ <- cg.successors(n)) {
            if(imdaf.update(getEntrySet(en), succ)){
              result += succ
            }
          }
        case xn : ICFGExitNode =>
          for (succ <- cg.successors(n)){
            val factsForCaller = callr.getAndMapFactsForCaller(getEntrySet(xn), succ, xn)
            imdaf.update(confluence(getEntrySet(succ), factsForCaller), succ)
            result += succ
          }
        case cn : ICFGCallNode =>
          if (imdaf.visit(cn)){
            result ++= cg.successors(n)
          }
        case rn : ICFGReturnNode =>
          for (succ <- cg.successors(n)) {
            if(imdaf.update(getEntrySet(n), succ)){
              result += succ
            }
          }
        case nn : ICFGNormalNode =>
          if (imdaf.visit(nn)){
            result ++= cg.successors(n)
          }
        case a => throw new RuntimeException("unexpected node type: " + a)
      }
      result
    }
    
    entrySetMap.put(flow.entryNode, iota)
    val workList = mlistEmpty[N]
    workList += flow.entryNode
    if(existingResult != null){
      //workList ++= existingResult.updateWorklist // later we will uncomment it
      existingResult.getInfluenceTo(gen, kill, callr)
    }
    while(!workList.isEmpty){      
      while (!workList.isEmpty) {        
        if(false){
          val newworkList = workList.par.map{
            n =>
              if(nl.isDefined) nl.get.onPreVisitNode(n, cg.predecessors(n))
              val newnodes = process(n)
              if(nl.isDefined) nl.get.onPostVisitNode(n, cg.successors(n))
              newnodes
          }.reduce(iunion[N])
          workList.clear
          workList ++= newworkList
        } else {
          val n = workList.remove(0)
          if(nl.isDefined) nl.get.onPreVisitNode(n, cg.predecessors(n))
          workList ++= process(n)
          if(nl.isDefined) nl.get.onPostVisitNode(n, cg.successors(n))
        }
      }
      val nodes = if(false) cg.nodes.par else cg.nodes
      workList ++= nodes.map{
        node =>
          var newnodes = isetEmpty[N]
          node match{
            case xn : ICFGExitNode =>
              if(nl.isDefined) nl.get.onPreVisitNode(xn, cg.predecessors(xn))
              val succs = cg.successors(xn)
              for (succ <- succs){
                val factsForCaller = callr.getAndMapFactsForCaller(getEntrySet(xn), succ, xn)
                if (imdaf.update(confluence(getEntrySet(succ), factsForCaller), succ))
                  newnodes += succ
              }
              if(nl.isDefined) nl.get.onPostVisitNode(xn, succs)
            case _ =>
          }
          newnodes
      }.reduce(iunion[N])
    }
    imdaf.setInfluenceFrom(gen, kill, callr)
    imdaf
    
  }
}
