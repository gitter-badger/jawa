package org.sireum.amandroid.objectFlowAnalysis

import org.sireum.util._
import org.sireum.amandroid.util.CombinationIterator

trait StringAnalyseModel[Node <: OfaNode, ValueSet <: NormalValueSet] {
  
  /**
   * contain all string operations and involved operation string parameter nodes and return nodes
   */
  var stringOperationTracker : Map[String, ProcedurePointNodes[Node]] = Map()
  def checkStringOperation(pUri : ResourceUri) : Boolean = {
    var flag : Boolean = true
    stringOperationTracker(pUri).paramEntryNodes.foreach{
      case(i, node) =>
    		if(node.getProperty[ValueSet]("ValueSet").isEmpty){
    		  flag = false
    		}
    }
    flag
  }
  
  def doStringOperation(fac :() => ValueSet) = {
    var result : Map[Node, ValueSet] = Map()
    stringOperationTracker.map{
      case (k, v) =>
        if(checkStringOperation(k)){
	        val strings : MList[ResourceUri] = mlistEmpty
	        val valueSets : Map[Int, ValueSet] = 
	          v.paramEntryNodes.map{
	          	case(i, node) => (i, node.getProperty[ValueSet]("ValueSet"))
		        }.toMap
	        val strsList = getStringList(valueSets)
	        val strs : Set[String] = if(!strsList.isEmpty && !strsList(0).isEmpty)strsList.map{l => applyStringOperation(k, strings ++ l)}.toSet
	        					               else Set()
	        v.retNodeOpt match{
	          case Some(r) =>
	            result += (r -> fac())
	            result(r).setInstance(Instance("[|java:lang:String|]", v.procPoint.getLoc), r.getContext)
	            result(r).setStrings(strs)
	          case None =>
	        }
        }
    }
    result
  }
  
  def getStringList(argsValueSets : Map[Int, ValueSet]) : List[List[String]] = {
    val lists = argsValueSets.toList.sortBy(_._1).map{case (k, v) => v.strings.toList}
    CombinationIterator.combinationIterator[ResourceUri](lists).toList
  }
  
  def isStringKind(name : String) : Boolean = name.equals("[|java:lang:StringBuilder|]") || name.equals("[|java:lang:String|]")
  
  def isStringOperation(sig : String) : Boolean = sig.contains("[|Ljava/lang/StringBuilder;.") || sig.contains("[|Ljava/lang/String;.")
  
	def applyStringOperation(sig : String, strings : MList[String]) : String = {
	  val size = strings.size
	  
	  sig match {
	    /*for stringbuilder.append*/
	    case "[|Ljava/lang/StringBuilder;.append:([C)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/StringBuilder;.append:(C)Ljava/lang/Appendable;|]" =>
	      require(strings.size == 1)
	      strings(0) + "char"
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/CharSequence;II)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/String;)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/StringBuilder;.append:(Z)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      strings(0) + "boolean"
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/CharSequence;)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/Object;)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      strings(0) + "object"
	    case "[|Ljava/lang/StringBuilder;.append:(D)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      strings(0) + "double"
	    case "[|Ljava/lang/StringBuilder;.append:(J)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      strings(0) + "long"
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/CharSequence;)Ljava/lang/Appendable;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/StringBuilder;.append:(C)Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      strings(0) + "char"
	    case "[|Ljava/lang/StringBuilder;.append:(Ljava/lang/CharSequence;II)Ljava/lang/Appendable;|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    /*end here*/
	    case "[|Ljava/lang/StringBuilder;.reverse:()Ljava/lang/StringBuilder;|]" =>
	      require(strings.size == 1)
	      new StringBuilder(strings(0)).reverse.toString
	    case "[|Ljava/lang/StringBuilder;.toString:()Ljava/lang/String;|]" =>
	      require(strings.size == 1)
	      strings(0)
	    /*for string*/
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/String;Ljava/lang/String;)V|]" =>
	      require(strings.size == 3)
	      strings(0) + strings(1) + strings(2)
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/String;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/StringBuilder;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/String;C)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([B)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "bytes"
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BLjava/nio/charset/Charset;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BIILjava/nio/charset/Charset;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V|]" =>
	      require(strings.size == 4)
	      strings(0) + strings(1) + strings(2) + strings(3)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BIII)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "bytes"
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/String;I)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BIILjava/lang/String;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BLjava/lang/String;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:()V|]" =>
	      require(strings.size == 1)
	      strings(0)
	    case "[|Ljava/lang/String;.&lt;init&gt;:([CII)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "chars"
	    case "[|Ljava/lang/String;.&lt;init&gt;:(Ljava/lang/StringBuffer;)V|]" =>
	      require(strings.size == 2)
	      strings(0) + strings(1)
	    case "[|Ljava/lang/String;.&lt;init&gt;:(II[C)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "chars"
	    case "[|Ljava/lang/String;.&lt;init&gt;:([III)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "ints"
	    case "[|Ljava/lang/String;.&lt;init&gt;:([C)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "chars"
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BI)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "bytes"
	    case "[|Ljava/lang/String;.&lt;init&gt;:([BII)V|]" =>
	      require(strings.size == 1)
	      strings(0) + "bytes"
	    case "[|Ljava/lang/String;.&lt;clinit&gt;:()V|]" =>
	      require(strings.size == 1)
	      strings(0)
//	    case "[|Ljava/lang/String;.split:(Ljava/lang/String;I)[Ljava/lang/String;|]" =>
//	      require(strings.size == 2)
//	      strings(0)).split(strings(1))
//	    case "[|Ljava/lang/String;.split:(Ljava/lang/String;)[Ljava/lang/String;|]" =>
	    case "[|Ljava/lang/String;.trim:()Ljava/lang/String;|]" => 
	      require(strings.size == 1)
	      strings(0).trim()
//	      "trim"
	    case "[|Ljava/lang/String;.intern:()Ljava/lang/String;|]" =>
	      require(strings.size == 1)
	      strings(0).intern()
//	      "intern"
	    case "[|Ljava/lang/String;.toLowerCase:()Ljava/lang/String;|]" =>
	      require(strings.size == 1)
	      strings(0).toLowerCase()
	    case "[|Ljava/lang/String;.toUpperCase:()Ljava/lang/String;|]" =>
	      require(strings.size == 1)
	      strings(0).toUpperCase()
	    case "[|Ljava/lang/String;.replaceAll:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;|]" =>
	      require(strings.size == 3)
	      strings(0).replaceAll(strings(1), strings(2))
	    case "[|Ljava/lang/String;.toString:()Ljava/lang/String;|]" =>
	      require(strings.size == 1)
	      strings(0)
	    case "[|Ljava/lang/String;.concat:(Ljava/lang/String;)Ljava/lang/String;|]" =>
	      require(strings.size == 2)
	      strings(0).concat(strings(1))
	    case "[|Ljava/lang/String;.replaceFirst:(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;|]" => 
	      require(strings.size == 3)
	      strings(0).replaceFirst(strings(1), strings(2))
	    /*
	     * [|Ljava/lang/String;.toLowerCase:(Ljava/util/Locale;)Ljava/lang/String;|]
	     * [|Ljava/lang/String;.toUpperCase:(Ljava/util/Locale;)Ljava/lang/String;|]
	     * [|Ljava/lang/String;.format:(Ljava/util/Locale;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;|]
	     * [|Ljava/lang/String;.format:(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;|]
	     * [|Ljava/lang/String;.replace:(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)Ljava/lang/String;|]
	     */
	    /*ends here*/
	    case _ =>
	      strings(0)
	  }
	    

	}
}