/*
Copyright (c) 2013-2014 Fengguo Wei & Sankardas Roy, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*/
package org.sireum.jawa.sjc

import org.sireum.util._

/**
 * This class is an jawa class representation of a pilar class. A JawaClass corresponds to a class or an interface of the source code. They are usually created by jawa Resolver.
 * You can also construct it manually.
 * 
 * @param typ object type of this class
 * @param accessFlags the access flags integer representation for this class
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */
class JawaClass(typ: ObjectType, accessFlags: Int) extends JavaKnowledge with ResolveLevel {
  import JawaClass._
  
  def this(typ: ObjectType, accessStr: String) = {
    this(typ, AccessFlag.getAccessFlags(accessStr))
  }
  
  /**
   * full name of this class: java.lang.Object or [Ljava.lang.Object;
   */
  def getName: String = typ.name
  /**
   * simple name of this class: Object or Object[]
   */
  def getSimpleName: String = typ.simpleName
  /**
   * canonical name of this class: java.lang.Object or java.lang.Object[]
   */
  def getCanonicalName: String = typ.canonicalName
  /**
   * package name of this class: java.lang
   */
  def getPackage: String = typ.pkg
  
  /**
   * is this class loaded or not
   */
  def isLoaded: Boolean = resolvingLevel <= ResolveLevel.NOT_LOADED
  
  /**
   * set of fields which declared in this class. map from field name to JawaField
   */
  protected val fields: MMap[String, JawaField] = mmapEmpty
  
  /**
   * set of methods which belong to this class. map from subsig to JawaMethod
   */
  protected val methods: MMap[String, JawaMethod] = mmapEmpty
  
  /**
   * set of interfaces which this class/interface implements/extends. map from interface name to JawaClass
   */
  protected val interfaces: MMap[String, JawaClass] = mmapEmpty
  
  /**
   * super class of this class. For interface it's always java.lang.Object
   */
  protected var superClass: JawaClass = null
  
  /**
   * outer class of this class
   */
  protected var outerClass: JawaClass = null
  
  /**
   * unknown means it's not available in our code repo
   */
  protected var unknown: Boolean = false
  
  def setUnknown = this.unknown = true
  
  /**
   * return true if this class is unknown class
   */
  def isUnknown = this.unknown
  
  /**
   * if the class is array type return true
   */
  def isArray: Boolean = typ.isArray
	
	/**
	 * return the access flags for this class
	 */
	def getAccessFlags = accessFlags
	
	/**
	 * return the access flags for this class
	 */
	def getAccessFlagString = AccessFlag.toString(getAccessFlags)
	
	/**
	 * return the number of fields declared in this class
	 */
	def fieldSize = this.fields.size
	
	/**
	 * get all the fields accessible from the class
	 */
	def getFields: ISet[JawaField] = {
    var results = getDeclaredFields
    var worklist: Set[JawaClass] = Set()
    worklist += this
    while(!worklist.isEmpty){
      worklist =
	      worklist.map{
	        rec =>
	          var parents = rec.getInterfaces
	          if(rec.hasSuperClass) parents += rec.getSuperClass
	          val fields =
		          if(!parents.isEmpty)
			          parents.map{
			          	parent =>
			          	  parent.getDeclaredFields.filter(f => !f.isPrivate && !results.exists(_.getName == f.getName))
			          }.reduce(iunion[JawaField])
			        else Set[JawaField]()
	          results ++= fields
	          parents
	      }.reduce(iunion[JawaClass])
    }
    results
  }
	
	/**
	 * get all the fields declared in this class
	 */
	
	def getDeclaredFields: ISet[JawaField] = this.fields.values.toSet
	
	/**
	 * get all static fields of the class
	 */
	
	def getStaticFields: ISet[JawaField] = getFields.filter(f => f.isStatic)
	
	/**
	 * get all non-static fields of the class
	 */
	def getNonStaticFields: ISet[JawaField] = getFields.filter(f => !f.isStatic)
	
	/**
	 * get all object type field
	 */
	def getObjectTypeFields: ISet[JawaField] = getFields.filter(f => f.isObject)
	
	/**
	 * get all non static and object type field
	 */
	def getNonStaticObjectTypeFields: ISet[JawaField] = getNonStaticFields.intersect(getObjectTypeFields)
	
	/**
	 * get all static and object type field
	 */
	def getStaticObjectTypeFields: ISet[JawaField] = getStaticFields.intersect(getObjectTypeFields)
	
	/**
	 * get all static fields of the class
	 */
	def getDeclaredStaticFields: ISet[JawaField] = getDeclaredFields.filter(f => f.isStatic)
	
	/**
	 * get all non-static fields of the class
	 */
	def getDeclaredNonStaticFields: ISet[JawaField] = getDeclaredFields.filter(f => !f.isStatic)
	
	/**
	 * get all object type field
	 */
	def getDeclaredObjectTypeFields: ISet[JawaField] = getDeclaredFields.filter(f => f.isObject)
	
	/**
	 * get all non static and object type field
	 */
	def getDeclaredNonStaticObjectTypeFields: ISet[JawaField] = getDeclaredNonStaticFields.intersect(getDeclaredObjectTypeFields)
	
	/**
	 * get all static and object type field
	 */
	def getDeclaredStaticObjectTypeFields: ISet[JawaField] = getDeclaredStaticFields.intersect(getDeclaredObjectTypeFields)
	
	/**
	 * add one field into the class
	 */
	def addField(field: JawaField) = {
    val fieldName = field.getName
	  if(declaresField(fieldName)) throw new RuntimeException("already declared: " + field.getName)
	  this.fields(fieldName) = field
	}
	
  /**
   * return true if the field is declared in this class
   */
	def declaresField(name: String): Boolean = !getDeclaredFields.filter(_.getName == name).isEmpty
	
	/**
   * return true if the field is declared in this class
   */
	def hasField(name: String): Boolean = !getFields.filter(_.getName == name).isEmpty
	
	/**
	 * removes the given field from this class
	 */
	def removeField(field: JawaField) = {
	  if(field.getDeclaringClass != this) throw new RuntimeException(getName + " did not declare " + field.getName)
	  this.fields -= field.getName
	}
	
	/**
	 * get field from this class by the given name
	 */
	def getField(name: String): JawaField = {
    if(!JawaField.isValidFieldName(name)) throw new RuntimeException("field name should not")
	  val fopt = getFields.find(_.getName == name)
	  fopt match{
	    case Some(f) => f
	    case None => 
        if(isUnknown){
          new JawaField(this, name, new ObjectType(JAVA_TOPLEVEL_OBJECT), AccessFlag.getAccessFlags("PUBLIC"))
        } else throw new RuntimeException("No field " + name + " in class " + getName)
	  }
	}
	
	/**
	 * get method from this class by the given subsignature
	 */
	def getMethod(subSig: String): JawaMethod = {
	  tryGetMethod(subSig) match{
      case Some(p) => p
      case None => 
        if(isUnknown){
          val sig = StringFormConverter.getSigFromOwnerAndMethodSubSig(getName, subSig)
          val proc = new JawaMethod().init(sig)
          addMethod(proc)
          proc
        } else throw new RuntimeException("No method " + subSig + " in class " + getName)
    }
	}
	
	/**
	 * try to get method from this class by the given subsignature
	 */
	
	def tryGetMethod(subSig: String): Option[JawaMethod] = {
	  this.methods.get(subSig)
	}
	
	/**
	 * get method from this class by the given subsignature
	 */
	
	def getMethodByName(procName: String): JawaMethod = {
	  if(!declaresMethodByName(procName)) throw new RuntimeException("No method " + procName + " in class " + getName)
	  var found = false
	  var foundMethod: JawaMethod = null
	  getMethods.foreach{
	    proc=>
	      if(proc.getName == procName){
	        if(found) throw new RuntimeException("ambiguous method" + procName)
	        else {
	          found = true
	          foundMethod = proc
	        }
	      }
	  }
	  if(found) foundMethod
	  else throw new RuntimeException("couldn't find method " + procName + "(*) in " + this)
	}
	
	/**
	 * get method from this class by the given subsignature
	 */
	
	def getMethodByShortName(procShortName: String): JawaMethod = {
	  if(!declaresMethodByShortName(procShortName)) throw new RuntimeException("No method " + procShortName + " in class " + getName)
	  var found = false
	  var foundMethod: JawaMethod = null
	  getMethods.foreach{
	    proc=>
	      if(proc.getShortName == procShortName){
	        if(found) throw new RuntimeException("ambiguous method " + procShortName)
	        else {
	          found = true
	          foundMethod = proc
	        }
	      }
	  }
	  if(found) foundMethod
	  else throw new RuntimeException("couldn't find method " + procShortName + "(*) in " + this)
	}
	
	/**
	 * get method from this class by the given method name
	 */
	
	def getMethodsByName(procName: String): Set[JawaMethod] = {
	  getMethods.filter(proc=> proc.getName == procName)
	}
	
	/**
	 * get method from this class by the given short proc name
	 */
	
	def getMethodsByShortName(procShortName: String): Set[JawaMethod] = {
	  getMethods.filter(proc=> proc.getShortName == procShortName)
	}
	
	/**
	 * get static initializer of this class
	 */
	
	def getStaticInitializer: JawaMethod = getMethodByShortName(this.staticInitializerName)
	
	/**
	 * whether this method exists in the class or not
	 */
	
	def declaresMethod(subSig: String): Boolean = this.subSigToMethods.contains(subSig)
	
	/**
	 * get method size of this class
	 */
	
	def getMethodSize: Int = this.methods.size
	
	/**
	 * get methods of this class
	 */
	
	def getMethods: ISet[JawaMethod] = this.methods.values.toSet
	
	/**
	 * get method by the given name, parameter types and return type
	 */
	
	def getMethod(name: String, paramTyps: List[String], returnTyp: Type): JawaMethod = {
	  var ap: JawaMethod = null
	  this.methods.foreach{
	    method=>
	      if(method.getName == name && method.getParamTypes == paramTyps && method.getReturnType == returnTyp) ap = method
	  }
	  if(ap == null) throw new RuntimeException("In " + getName + " does not have method " + name + "(" + paramTyps + ")" + returnTyp)
	  else ap
	}
	
	/**
	 * does method exist with the given name, parameter types and return type?
	 */
	
	def declaresMethod(name: String, paramTyps: List[String], returnTyp: Type): Boolean = {
	  var find: Boolean = false
	  this.methods.foreach{
	    proc=>
	      if(proc.getName == name && proc.getParamTypes == paramTyps && proc.getReturnType == returnTyp) find = true
	  }
	  find
	}
	
	/**
	 * does method exist with the given name and parameter types?
	 */
	
	def declaresMethod(name: String, paramTyps: List[String]): Boolean = {
	  var find: Boolean = false
	  this.methods.foreach{
	    proc=>
	      if(proc.getName == name && proc.getParamTypes == paramTyps) find = true
	  }
	  find
	}
	
	/**
	 * does method exists with the given name?
	 */
	
	def declaresMethodByName(name: String): Boolean = {
	  var find: Boolean = false
	  this.methods.foreach{
	    proc=>
	      if(proc.getName == name) find = true
	  }
	  find
	}
	
	/**
	 * does method exists with the given short name?
	 */
	
	def declaresMethodByShortName(name: String): Boolean = {
	  var find: Boolean = false
	  this.methods.foreach{
	    proc=>
	      if(proc.getShortName == name) find = true
	  }
	  find
	}
	
	/**
	 * return true if this class has static initializer
	 */
	
	def declaresStaticInitializer: Boolean = declaresMethodByShortName(this.staticInitializerName)
	
	/**
	 * add the given method to this class
	 */
	
	def addMethod(ap: JawaMethod) = {
	  if(ap.isDeclared) throw new RuntimeException(ap.getName + " is already declared in class " + ap.getDeclaringClass.getName)

	  if(this.subSigToMethods.contains(ap.getSubSignature)) throw new RuntimeException("The method " + ap.getName + " is already declared in class " + getName)
	  this.subSigToMethods += (ap.getSubSignature -> ap)
	  this.methods += ap
	  ap.setDeclaringClass(this)
	}
	
	/**
	 * remove the given method from this class
	 */
	
	def removeMethod(ap: JawaMethod) = {
	  if(!ap.isDeclared || ap.getDeclaringClass != this) throw new RuntimeException("Not correct declarer for remove: " + ap.getName)
	  if(!this.subSigToMethods.contains(ap.getSubSignature)) throw new RuntimeException("The method " + ap.getName + " is not declared in class " + getName)
	  this.subSigToMethods -= ap.getSubSignature
	  this.methods -= ap
	  ap.clearDeclaringClass
	}
	
	/**
	 * get interface size
	 */
	
	def getInterfaceSize: Int = this.interfaces.size
	
	/**
	 * get interfaces
	 */
	
	def getInterfaces: ISet[JawaClass] = this.interfaces.values.toSet
	
	/**
	 * whether this class implements the given interface
	 */
	def implementsInterface(name: String): Boolean = {
	  this.interfaces.contains(name)
	}
	
	/**
	 * add an interface which is directly implemented by this class
	 */
	
	def addInterface(i: JawaClass) = {
    if(!i.isInterface) throw new RuntimeException("This is not an interface:" + i)
    if(implementsInterface(i.getName)) throw new RuntimeException(this + " already implements interface " + i)
	  this.interfaces(i.getName) = i
	}
	
	/**
	 * remove an interface from this class
	 */
	def removeInterface(i: JawaClass) = {
    if(!i.isInterface) throw new RuntimeException("This is not an interface:" + i)
	  if(!implementsInterface(i.getName)) throw new RuntimeException(this + " not implements interface " + i.getName)
	  this.interfaces -= i.getName
	}
	
	/**
	 * whether the current class has a super class or not
	 */
	def hasSuperClass = this.superClass != null
	
	/**
	 * get the super class
	 */
	def getSuperClass: JawaClass = {
	  if(!hasSuperClass) throw new RuntimeException("no super class for " + getName)
	  this.superClass
	}
	
	/**
	 * try to get the super class
	 */
	def tryGetSuperClass: Option[JawaClass] = {
	  if(hasSuperClass) Some(this.superClass)
	  else None
	}
	
	/**
	 * set super class
	 */
	def setSuperClass(sc: JawaClass) = {
	  this.superClass = sc
	}
	
	/**
	 * whether the current class has an outer class or not
	 */
	def hasOuterClass = this.outerClass != null
	
	/**
	 * get the outer class
	 */
	def getOuterClass: JawaClass = {
	  if(!hasOuterClass) throw new RuntimeException("no outer class for: " + getName)
	  else this.outerClass
	}
	
	/**
	 * try to get the outer class
	 */
	def tryGetOuterClass: Option[JawaClass] = {
	  if(!hasOuterClass) None
	  else Some(this.outerClass)
	}
	
	/**
	 * set outer class
	 */
	def setOuterClass(oc: JawaClass) = {
	  this.outerClass = oc
	}
	
	/**
	 * whether current class is an inner class or not
	 */
	def isInnerClass: Boolean = hasOuterClass
	
	/**
   * return true if this class is an interface
   */
  def isInterface: Boolean = AccessFlag.isInterface(this.accessFlags)
	
	/**
   * return true if this class is abstract
   */
  def isAbstract: Boolean = AccessFlag.isAbstract(this.accessFlags)
  
  /**
   * return true if this class is concrete
   */
  def isConcrete: Boolean = !isInterface && !isAbstract
  
  /**
   * return true if this class is public
   */
  def isPublic: Boolean = AccessFlag.isPublic(this.accessFlags)
  
  /**
   * return true if this class is private
   */
  def isPrivate: Boolean = AccessFlag.isPrivate(this.accessFlags)
  
  /**
   * return true if this class is protected
   */
  def isProtected: Boolean = AccessFlag.isProtected(this.accessFlags)
  
  /**
   * return true if this class is final
   */
  def isFinal: Boolean = AccessFlag.isFinal(this.accessFlags)
  
  /**
   * return true if this class is static
   */
  def isStatic: Boolean = AccessFlag.isStatic(this.accessFlags)
  
  /**
   * return true if it's a child of given class
   */
  def isChildOf(clazzName: String): Boolean = {
    Center.tryGetClass(clazzName) match {
      case Some(c) => isChildOf(c)
      case None => false
    }
  }
  
  /**
   * return true if it's a child of given class
   */
  def isChildOf(clazz: JawaClass): Boolean = {
	  Center.getClassHierarchy.getAllSuperClassesOf(this).contains(clazz)
	}
  
  /**
   * is this class an application class
   */
  def isApplicationClass: Boolean = Center.getApplicationClasses.contains(this)
  
  /**
   * set this class as an application class
   */
  def setApplicationClass = {
	  val c = Center.getContainingSet(this)
	  if(c != null) Center.removeFromContainingSet(this)
	  Center.addApplicationClass(this)
	}
	
	/**
   * is this class  a framework class
   */
  def isFrameworkClass: Boolean = Center.getFrameworkClasses.contains(this)
  
  /**
   * is this class  a third party lib class
   */
  def isThirdPartyLibClass: Boolean = Center.getThirdPartyLibClasses.contains(this)
  
  
  /**
   * set this class as a framework class
   */
  def setFrameworkClass = {
	  val c = Center.getContainingSet(this)
	  if(c != null) Center.removeFromContainingSet(this)
	  Center.addFrameworkClass(this)
	}
  
  /**
   * set this class as a third party lib class
   */
  def setThirdPartyLibClass = {
    val c = Center.getContainingSet(this)
    if(c != null) Center.removeFromContainingSet(this)
    Center.addThirdPartyLibClass(this)
  }
  
  /**
   * whether this class is a java library class
   */
  def isJavaLibraryClass: Boolean = 
    getPackage.startsWith("java.") ||
    getPackage.startsWith("sun.") ||
    getPackage.startsWith("javax.") ||
    getPackage.startsWith("com.sun.") ||
    getPackage.startsWith("org.omg.") ||
    getPackage.startsWith("org.xml.")
    
    
  /**
	 * retrieve code belong to this class
	 */
	def retrieveCode = JawaCodeSource.getClassCode(getName, ResolveLevel.BODY)
	
	/**
	 * update resolving level for current class
	 */
	def updateResolvingLevel = {
    setResolvingLevel(getMethods.map(_.getResolvingLevel).reduceLeft((x, y) => if(x < y) x else y))
  }
	
	def printDetail = {
    println("++++++++++++++++AmandroidClass++++++++++++++++")
    println("recName: " + getName)
    println("package: " + getPackage)
    println("simpleName: " + getSimpleName)
    println("CanonicalName: " + getCanonicalName)
    println("superClass: " + tryGetSuperClass)
    println("outerClass: " + tryGetOuterClass)
    println("interfaces: " + getInterfaces)
    println("accessFlags: " + getAccessFlagString)
    println("isLoaded: " + isLoaded)
    println("fields: " + getFields)
    println("methods: " + getMethods)
    println("++++++++++++++++++++++++++++++++")
  }
	
  override def toString: String = getName
}

object JawaClass {

}