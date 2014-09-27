/*
Copyright (c) 2013-2014 Fengguo Wei & Sankardas Roy, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*/
package org.sireum.jawa.xml;

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 */
public class AndroidScalaCollection {

  public AndroidScalaCollectionType typ;
  public Object[] elements;

  public AndroidScalaCollection(AndroidScalaCollectionType type, Object[] elements) {
    this.typ = type;
    this.elements = elements;
  }
}