package org.sireum.jawa.lexer

case class TokenType(name: String) {

//  def isNewline = this == Tokens.NEWLINE || this == Tokens.NEWLINES

  def isKeyword = Tokens.KEYWORDS contains this

  def isComment = Tokens.COMMENTS contains this

  def isId = Tokens.IDS contains this

  def isLiteral = Tokens.LITERALS contains this

  override lazy val toString = name

}