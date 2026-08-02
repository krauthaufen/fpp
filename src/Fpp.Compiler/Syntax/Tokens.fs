namespace Fpp.Syntax

/// Trivia is every piece of source text that is not a token: whitespace,
/// newlines, comments. Kept verbatim so trees are lossless.
type TriviaKind =
    | Whitespace
    | Newline
    | LineComment
    | BlockComment

type Trivia =
    { TriviaKind : TriviaKind
      TriviaText : string }

type TokenKind =
    | Ident
    | Keyword
    | IntLit
    | FloatLit
    | StringLit
    | CharLit
    /// Symbolic operators and punctuation-like symbols (".", ":", "|", "->", ...).
    /// The parser refines by text; the lexer stays coarse.
    | Operator
    | LParen
    | RParen
    | LBracket
    | RBracket
    | LBrace
    | RBrace
    | Comma
    | Semicolon
    | Eof
    /// A character the lexer could not classify. Never dropped — error
    /// tolerance means the tree still round-trips.
    | Unknown

/// A token owns its leading and trailing trivia (Roslyn convention: trailing
/// trivia extends up to and including the first newline; everything after
/// belongs to the next token's leading trivia). Concatenating
/// leading + text + trailing over all tokens reproduces the source exactly.
type Token =
    { Kind : TokenKind
      Text : string
      Leading : Trivia list
      Trailing : Trivia list
      /// Byte offset of Text within the source (excludes leading trivia).
      Offset : int }

module Keywords =

    let all : Set<string> =
        Set.ofList [
            "abstract"; "and"; "as"; "assert"; "base"; "begin"; "class"
            "default"; "delegate"; "do"; "done"; "downcast"; "downto"; "elif"
            "else"; "end"; "exception"; "extern"; "false"; "finally"; "fixed"
            "for"; "fun"; "function"; "global"; "if"; "in"; "inherit"; "inline"
            "interface"; "internal"; "lazy"; "let"; "match"; "member"; "module"
            "mutable"; "namespace"; "new"; "not"; "null"; "of"; "open"; "or"
            "override"; "private"; "public"; "rec"; "return"; "static"
            "struct"; "then"; "to"; "true"; "try"; "type"; "upcast"; "use"
            "val"; "void"; "when"; "while"; "with"; "yield"
        ]

    let isKeyword (s : string) : bool = Set.contains s all
