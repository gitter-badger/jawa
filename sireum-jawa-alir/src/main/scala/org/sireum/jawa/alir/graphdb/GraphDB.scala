package org.sireum.jawa.alir.graphdb

import com.tinkerpop.blueprints.impls.orient.OrientGraphFactory
import com.tinkerpop.blueprints.impls.orient.OrientGraph
import org.sireum.jawa.alir.interProcedural.InterProceduralNode
import com.tinkerpop.blueprints.Vertex
import org.sireum.jawa.alir.interProcedural.InterProceduralGraph
import org.sireum.alir.AlirEdge
import com.tinkerpop.blueprints.Edge
import org.sireum.util._
import org.sireum.jawa.alir.controlFlowGraph.CGNode
import org.sireum.jawa.alir.dataDependenceAnalysis.IDDGNode
import org.sireum.jawa.alir.dataDependenceAnalysis.InterProceduralDataDependenceGraph
import org.sireum.jawa.alir.controlFlowGraph.InterproceduralControlFlowGraph
import org.sireum.jawa.alir.interProcedural.InterProceduralDataFlowGraph
import com.orientechnologies.orient.core.metadata.schema.OType
import org.sireum.jawa.alir.controlFlowGraph._
import java.util.regex.Pattern
import com.tinkerpop.blueprints.impls.orient.OrientVertex
import com.tinkerpop.blueprints.impls.orient.OrientEdge

class GraphDB(dir : String, username : String, password : String) {
  
  val factory : OrientGraphFactory = new OrientGraphFactory(dir, username, password)
  
  /**
   * Init Orient DB's data structure for storing IDFG
   */
  def initForIdfg = {
    val graph : OrientGraph = factory.getTx()
    try{
      if(graph.getVertexType("ICFGNode") == null){
        graph.createVertexType("ICFGNode", "V")
        val iNode = graph.getVertexType("ICFGNode")
        iNode.createProperty("apk", OType.STRING)
        iNode.createProperty("owner", OType.STRING)
        iNode.createProperty("context", OType.STRING)
        iNode.createProperty("code", OType.STRING)
        iNode.createProperty("facts", OType.EMBEDDEDSET)
      }
      if(graph.getVertexType("ICFGVirtualNode") == null){
        graph.createVertexType("ICFGVirtualNode", "ICFGNode")
      }
      if(graph.getVertexType("ICFGEntryNode") == null){
        graph.createVertexType("ICFGEntryNode", "ICFGVirtualNode")
      }
      if(graph.getVertexType("ICFGExitNode") == null){
        graph.createVertexType("ICFGExitNode", "ICFGVirtualNode")
      }
      if(graph.getVertexType("ICFGCenterNode") == null){
        graph.createVertexType("ICFGCenterNode", "ICFGVirtualNode")
      }
      
      if(graph.getVertexType("ICFGLocNode") == null){
        graph.createVertexType("ICFGLocNode", "ICFGNode")
      }
      
      if(graph.getVertexType("ICFGInvokeNode") == null){
        graph.createVertexType("ICFGInvokeNode", "ICFGLocNode")
        
        val iiNode = graph.getVertexType("ICFGInvokeNode")
        iiNode.createProperty("signature", OType.STRING)
        iiNode.createProperty("callees", OType.EMBEDDEDSET)
      }
      
      if(graph.getVertexType("ICFGCallNode") == null){
        graph.createVertexType("ICFGCallNode", "ICFGInvokeNode")
      }
      if(graph.getVertexType("ICFGReturnNode") == null){
        graph.createVertexType("ICFGReturnNode", "ICFGInvokeNode")
      }
      
      if(graph.getVertexType("ICFGNormalNode") == null){
        graph.createVertexType("ICFGNormalNode", "ICFGLocNode")
      }
      
      if(graph.getVertexType("ICFGConditionNode") == null){
        graph.createVertexType("ICFGConditionNode", "ICFGLocNode")
        val icNode = graph.getVertexType("ICFGConditionNode")
        icNode.createProperty("condition", OType.STRING)
      }
      
      if(graph.getEdgeType("ICFGEdge") == null){
        graph.createEdgeType("ICFGEdge", "E")
      }
    } finally {
      graph.shutdown()
    }
  }

  def storeIcfg[Node <: CGNode](app : String, owner : String, g : InterproceduralControlFlowGraph[Node]) = {
    /**
     * a cache map between context and it's vetex id
     */
    val cache : MMap[Int, Object] = mmapEmpty
    val graph : OrientGraph = factory.getTx()
    try {
      val vs = graph.getVertices("owner", owner)
      val es = graph.getEdges("owner", owner)
      import collection.JavaConversions._
      vs.foreach(_.remove())
      startTransactions_icfg[Node](app, owner, g, graph, cache)
    } finally {
      graph.shutdown()
    }
  }
  
  private def startTransactions_icfg[Node <: CGNode](app : String, owner : String, g : InterproceduralControlFlowGraph[Node], graph : OrientGraph, cache : MMap[Int, Object]) = {
    try{
      g.nodes.foreach{
        node =>
          insertNode_icfg(app, owner, graph, node, cache)
      }
      g.edges.foreach{
        edge =>
          insertEdge_icfg(app, owner, graph, edge, cache)
      }
      graph.commit()
    } catch {
      case e : Exception =>
        e.printStackTrace()
        graph.rollback()
    }
  }
  
  private def insertNode_icfg[Node <: CGNode](app : String, owner : String, graph : OrientGraph, node : Node, cache : MMap[Int, Object]) : OrientVertex = {
    val vex : OrientVertex = 
      node match{
        case n : CGEntryNode =>
          val v = graph.addVertex("class:ICFGEntryNode", Nil:_*)
          v
        case n : CGExitNode =>
          val v = graph.addVertex("class:ICFGExitNode", Nil:_*)
          v
        case n : CGCenterNode =>
          val v = graph.addVertex("class:ICFGCenterNode", Nil:_*)
          v
        case n : CGCallNode =>
          val v = graph.addVertex("class:ICFGCallNode", Nil:_*)
          v.setProperty("signature", n.getSignature)
          import scala.collection.JavaConverters._
          import scala.collection.JavaConversions._
          v.setProperty("callees", n.getCalleeSet.map(_.callee).asJava)
          v
        case n : CGReturnNode =>
          val v = graph.addVertex("class:ICFGReturnNode", Nil:_*)
          v.setProperty("signature", n.getSignature)
          import scala.collection.JavaConverters._
          import scala.collection.JavaConversions._
          v.setProperty("callees", n.getCalleeSet.map(_.callee).asJava)
          v
        case n : CGNormalNode =>
          val code = n.getCode
          val pattern = Pattern.compile("if\\s(.+)\\sthen\\sgoto")
          val matcher = pattern.matcher(code)
          val v =
            if(matcher.find()){
              val tv = graph.addVertex("class:ICFGConditionNode", Nil:_*)
              tv.setProperty("condition", matcher.group(1))
              tv
            }
            else 
              graph.addVertex("class:ICFGNormalNode", Nil:_*)
          v
        case a =>
          throw new RuntimeException("Unexpected Node Type: " + a.getClass())
      }
    vex.setProperty("apk", app)
    vex.setProperty("owner", owner)
    vex.setProperty("context", node.getContext.toString())
    vex.setProperty("code", node.asInstanceOf[CGNode].getCode)
    cache += (node.hashCode() -> vex.getId())
    vex
  }
  
  private def insertEdge_icfg[Node <: CGNode](app : String, owner : String, graph : OrientGraph, e : AlirEdge[Node], cache : MMap[Int, Object]) : OrientEdge = {
    val srcid = cache.getOrElse(e.source.hashCode(), throw new RuntimeException("Could not find vetex of node: " + e.source.getContext))
    val dstid = cache.getOrElse(e.target.hashCode(), throw new RuntimeException("Could not find vetex of node: " + e.target.getContext))
    val src = graph.getVertex(srcid)
    val dst = graph.getVertex(dstid)
    val edge : OrientEdge = graph.addEdge("class:ICFGEdge", src, dst, null)
    edge.setProperty("apk", app)
    edge.setProperty("owner", owner)
    edge
  }
  
  def storeIdfg(app : String, owner : String, g : InterProceduralDataFlowGraph) = {
    /**
     * a cache map between context and it's vetex id
     */
    val cache : MMap[Int, Object] = mmapEmpty
    val graph : OrientGraph = factory.getTx()
    try {
      val vs = graph.getVertices("owner", owner)
      import collection.JavaConversions._
      vs.foreach(_.remove())
      startTransactions_idfg(app, owner, g, graph, cache)
    } finally {
      graph.shutdown()
    }
  }
  
  private def startTransactions_idfg(app : String, owner : String, g : InterProceduralDataFlowGraph, graph : OrientGraph, cache : MMap[Int, Object]) = {
    try{
      val icfg = g.icfg
      val rfaRes = g.summary
      var i = 0
      icfg.nodes.foreach{
        node =>
          i = i + 1
          val vex = insertNode_icfg(app, owner, graph, node, cache)
          val facts = rfaRes.entrySet(node)
          val fs : Set[String] = 
            if(!facts.isEmpty && facts != null) facts.map(f => f.s + "->" + f.v)
            else Set()
          import scala.collection.JavaConverters._
          import scala.collection.JavaConversions._
          vex.setProperty("facts", fs.asJava)
          if(i%100 == 0)
            graph.commit()
      }
      i = 0
      graph.commit()
      icfg.edges.foreach{
        edge =>
          i = i + 1
          insertEdge_icfg(app, owner, graph, edge, cache)
          if(i%100 == 0)
            graph.commit()
      }
      graph.commit()
    } catch {
      case e : Exception =>
        e.printStackTrace()
        graph.rollback()
    }
  }
  
}