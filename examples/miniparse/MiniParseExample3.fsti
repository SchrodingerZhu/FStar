module MiniParseExample3
open MiniParse.Tac.Spec
open MiniParse.Impl.Base

module U8 = FStar.UInt8

type color = | Red | Blue | Green | Yellow
type palette = nlist 18 U8.t // color // * U8.t)

val ps: package palette

val p: parser_impl (package_parser ps)