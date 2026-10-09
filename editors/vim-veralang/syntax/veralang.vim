" Vim syntax file
" Language:    Vera
" Filetype:    veralang -- "vera" which collides with Vim's built-in
"              Synopsys Vera syntax; see README.md.
" Ported from: editors/vscode/syntaxes/vera.tmLanguage.json

if exists("b:current_syntax")
	finish
endif

syntax sync fromstart

" Last match wins.

" Numeric literals
syntax match veraInteger '\<\d\+\>'
syntax match veraFloat '\<\d\+\.\d\+\%([eE][+-]\=\d\+\)\=\>'

" Type-argument list, nested to three levels: <Int>, <Option<Int>>,
" <String, Array<Option<Int>>>. Vim patterns do not recurse, so the depth
" is spelled out, and three covers what Vera writes in practice. Beyond
" that the slot match simply does not reach the closing brackets and the
" veraGenericArgs region below picks them up instead — measured on
" @Map<A, Map<B, Map<C, Option<D>>>>, where every bracket is still
" highlighted, as a generic bracket rather than as part of the slot.
let s:angles = '<\%([^<>]\|<\%([^<>]\|<[^<>]*>\)*>\)*>'

" Slot references: @Type.index, @Type.result, and @Type bindings. The
" lookahead also accepts "->", "=", and a bare ">" so a slot type is still
" recognized before a signature's return arrow ("(@Color -> @Bool)"), a let
" binding ("let @List<Int> = ..."), and the close of a tuple destructure
" ("Tuple<@String, @Int>").
execute 'syntax match veraSlotRef ' .
      \ string('@[A-Z][A-Za-z0-9_]*\%(' . s:angles . '\)*\.\%(result\|\d\+\)')
execute 'syntax match veraSlotBinding ' .
      \ string('@[A-Z][A-Za-z0-9_]*\%(' . s:angles .
      \        '\)*\ze\s*\%([,)\]}=>]\|->\)')

" Keywords
syntax keyword veraStorageModifier public private
syntax keyword veraKeywordDecl fn data type effect ability module import
syntax keyword veraContractKeyword requires ensures effects decreases invariant
syntax keyword veraForall forall
syntax keyword veraKeywordControl if then else match let in where handle resume with
syntax keyword veraOpKeyword op
syntax keyword veraConstant true false pure
syntax keyword veraWildcard _

" Balanced parentheses.
syntax region veraParens start='(' end=')' transparent contains=TOP

" Language constants
syntax match veraUnit '()'
" Typed hole: standalone "?", not part of "??" or a word.
syntax match veraHole '\%(\w\|?\)\@<!?\%(\w\|?\)\@!'

" Built-in types and effects
syntax keyword veraPrimitiveType Bool Int Nat Float64 Byte String Unit Never
syntax keyword veraCompositeType Array Option Map Set Tuple Result Decimal Json Future Fn Ordering
syntax keyword veraAdtType MdBlock MdInline UrlParts HtmlNode Request Response
" Every effect in `vera effects --json`. The four abilities it also
" lists (Eq, Hash, Ord, Show) are absent from every editor grammar; whether
" they should highlight distinctly from ordinary types is tracked in #1295.
syntax keyword veraEffectType IO State Exn Http HttpServer Async Diverge Inference Random DB

" Fallback: any bare capitalized identifier is at minimum a type reference.
" This covers type variables like the T in "data List<T>" and user type names
" used as a field/parameter type (e.g. List in "Cons(T, List<T>)").
syntax match veraTypeRef '\<[A-Z][A-Za-z0-9_]*\>'

" Qualified effect operations: IO.print, State.put, ...
syntax match veraEffectOpType '\<[A-Z][A-Za-z0-9_]*\>\ze\.[a-z_][a-z_0-9]*\>'
syntax match veraEffectOpName '\<[A-Z][A-Za-z0-9_]*\.\zs[a-z_][a-z_0-9]*\>'

" Module-qualified calls: module.name::function
syntax match veraNamespacePath '\<[a-z][a-z0-9_.]*\ze::[a-z_][a-z_0-9]*\>'
syntax match veraNamespaceFunc '[a-z][a-z0-9_.]*::\zs[a-z_][a-z_0-9]*\>'

" Fixed ADT constructors
syntax keyword veraConstructor Some None Ok Err Less Equal Greater
syntax keyword veraConstructor JNull JBool JNumber JString JArray JObject
syntax keyword veraConstructor HtmlElement HtmlText HtmlComment
syntax keyword veraConstructor MdParagraph MdHeading MdCodeBlock MdBlockQuote MdList MdThematicBreak MdTable MdDocument
syntax keyword veraConstructor MdText MdCode MdEmph MdStrong MdLink MdImage

" User-defined constructors: heuristic -- capitalized identifier immediately
" followed by ( , or ).
syntax match veraTag '\<[A-Z][A-Za-z0-9_]*\>\ze\s*[(,)]'

" Function calls: lowercase identifier immediately followed by (.
syntax match veraFunctionCall '\<[a-z_][a-z_0-9]*\>\ze\s*('

" Quantifiers and contract words only count as such immediately before "(".
" Bare "forall" is caught by veraKeywordDecl above.
syntax match veraQuantifier '\<\%(forall\|exists\)\>\ze\s*('
syntax match veraContractWord '\<\%(old\|new\|assert\|assume\)\>\ze\s*('

" Declaration names.
syntax match veraFunctionDefName '\%(\<fn\s\+\)\@<=[a-z_][a-z_0-9]*\>'
syntax match veraTypeDefName '\%(\<data\s\+\)\@<=[A-Z][A-Za-z0-9_]*\>'
syntax match veraEffectDefName '\%(\<effect\s\+\)\@<=[A-Z][A-Za-z0-9_]*\>'
syntax match veraAbilityDefName '\%(\<ability\s\+\)\@<=[A-Z][A-Za-z0-9_]*\>'
syntax match veraTypeAliasDefName '\%(\<type\s\+\)\@<=[A-Z][A-Za-z0-9_]*\>'
syntax match veraModuleName '\%(\<module\s\+\)\@<=[a-z][a-z0-9_.]*'
syntax match veraImportName '\%(\<import\s\+\)\@<=[a-z][a-z0-9_.]*'

" Operators
syntax match veraOpArith '[+\-*/%]'
syntax match veraOpLogical '||\|&&\|!'
syntax match veraOpAssign '=\%(=\)\@!'
syntax match veraOpComparison '==\|!=\|<=\|>=\|<\|>'
syntax match veraOpImplies '==>'
syntax match veraOpArrow '->'
syntax match veraOpPipe '|>'

" Generic argument brackets: List<T>, Array<Option<A>>, and bare effect sets
" like effects(<IO, Async>).
"
" A region rather than a per-character match, because only a region nests.
" The previous one-character lookbehind ('\%(\w\|(\)\@<=[<>]') got both
" ends of this wrong: in Map<String, Array<Option<Int>>> the two outer
" closers follow a '>' rather than a word character, so they fell through
" to veraOpComparison and highlighted as operators; and in an unspaced
" comparison like requires(x<y) the '<' does follow a word character, so
" it was claimed as a bracket. Anchoring the start on a capitalised
" identifier fixes the second — Vera type names are capitalised (spec
" §2), operands in a comparison are slots or lowercase — and letting the
" region contain itself fixes the first.
syntax region veraGenericArgs matchgroup=veraGenericBracket
      \ start='\%(\<[A-Z][A-Za-z0-9_]*\)\@<=<'
      \ end='>' oneline contains=TOP

" Bare effect set: the '<' opens immediately after '(', with no type name
" in front of it, so it needs its own start pattern.
syntax region veraEffectSet matchgroup=veraGenericBracket
      \ start='(\@<=<'
      \ end='>' oneline contains=TOP

syntax match veraTerminator ';'

" Strings and comments
" Nestable block comment: {- ... {- ... -} ... -}
syntax region veraBlockComment start='{-' end='-}' contains=veraBlockComment,@Spell

" Annotation comment: /* ... */
syntax region veraAnnotationComment start='/\*' end='\*/' contains=@Spell

syntax region veraString start='"' skip='\\.' end='"' contains=veraStringEscape,veraInterpolation
syntax match veraStringEscape '\\[nrt\\"0]' contained
syntax region veraInterpolation matchgroup=veraInterpolationDelim start='\\(' end=')' contained contains=TOP

syntax match veraLineComment '--.*$' contains=@Spell

" Highlighting
highlight default link veraLineComment Comment
highlight default link veraBlockComment Comment
highlight default link veraAnnotationComment SpecialComment
highlight default link veraString String
highlight default link veraStringEscape SpecialChar
highlight default link veraInterpolationDelim Delimiter

highlight default link veraSlotRef Special
highlight default link veraSlotBinding Special

highlight default link veraInteger Number
highlight default link veraFloat Float

highlight default link veraStorageModifier StorageClass
highlight default link veraKeywordDecl Keyword
highlight default link veraContractKeyword PreProc
highlight default link veraForall Keyword
highlight default link veraQuantifier Keyword
highlight default link veraContractWord PreProc
highlight default link veraKeywordControl Conditional
highlight default link veraOpKeyword Keyword
highlight default link veraConstant Boolean
highlight default link veraWildcard Special

highlight default link veraUnit Constant
highlight default link veraHole Special

highlight default link veraPrimitiveType Type
highlight default link veraCompositeType Type
highlight default link veraAdtType Type
highlight default link veraEffectType Structure
highlight default link veraEffectOpType Structure
highlight default link veraEffectOpName Function

highlight default link veraNamespacePath Identifier
highlight default link veraNamespaceFunc Function

highlight default link veraConstructor Constant
highlight default link veraTag Type
highlight default link veraTypeRef Type
highlight default link veraFunctionCall Function

highlight default link veraFunctionDefName Function
highlight default link veraTypeDefName Type
highlight default link veraEffectDefName Structure
highlight default link veraAbilityDefName Type
highlight default link veraTypeAliasDefName Type
highlight default link veraModuleName Identifier
highlight default link veraImportName Identifier

highlight default link veraOpArith Operator
highlight default link veraOpLogical Operator
highlight default link veraOpAssign Operator
highlight default link veraOpComparison Operator
highlight default link veraOpImplies Operator
highlight default link veraOpArrow Operator
highlight default link veraOpPipe Operator
highlight default link veraGenericBracket Delimiter
highlight default link veraTerminator Delimiter

let b:current_syntax = "veralang"
