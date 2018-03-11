open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____7 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____7
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____11 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____11
  
let map_opt :
  'Auu____16 'Auu____17 .
    Prims.unit ->
      ('Auu____16 -> 'Auu____17 FStar_Pervasives_Native.option) ->
        'Auu____16 Prims.list -> 'Auu____17 Prims.list
  = fun uu____31  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____36 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____36
      then
        let uu____37 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.strcat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____37
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____41 .
    ('Auu____41,FStar_Syntax_Syntax.arg_qualifier
                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____41,FStar_Syntax_Syntax.arg_qualifier
                    FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___65_95  ->
            match uu___65_95 with
            | (uu____102,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____103)) -> false
            | uu____106 -> true))
  
let filter_pattern_imp :
  'Auu____115 .
    ('Auu____115,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____115,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____145  ->
         match uu____145 with
         | (uu____150,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
  
let (resugar_arg_qual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
        if b
        then FStar_Pervasives_Native.None
        else
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
  
let (resugar_imp :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Parser_AST.imp)
  =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        FStar_Parser_AST.Hash
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
        FStar_Parser_AST.Nothing
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        FStar_Parser_AST.Nothing
  
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____214 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____222 = FStar_Options.print_universes ()  in
    if uu____222
    then
      let uu____223 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____223 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____263 ->
          let uu____264 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____264 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____271 =
                      let uu____272 =
                        let uu____273 =
                          let uu____284 = FStar_Util.string_of_int n1  in
                          (uu____284, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____273  in
                      FStar_Parser_AST.Const uu____272  in
                    mk1 uu____271 r
                | uu____295 ->
                    let e1 =
                      let uu____297 =
                        let uu____298 =
                          let uu____299 =
                            let uu____310 = FStar_Util.string_of_int n1  in
                            (uu____310, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____299  in
                        FStar_Parser_AST.Const uu____298  in
                      mk1 uu____297 r  in
                    let e2 = resugar_universe u1 r  in
                    mk1
                      (FStar_Parser_AST.Op
                         ((FStar_Ident.id_of_text "+"), [e1; e2])) r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____327 ->
               let t =
                 let uu____331 =
                   let uu____332 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____332  in
                 mk1 uu____331 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____338 =
                        let uu____339 =
                          let uu____346 = resugar_universe x r  in
                          (acc, uu____346, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____339  in
                      mk1 uu____338 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____348 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____359 =
              let uu____364 =
                let uu____365 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____365  in
              (uu____364, r)  in
            FStar_Ident.mk_ident uu____359  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string,Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___66_388 =
      match uu___66_388 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____565 -> FStar_Pervasives_Native.None  in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | uu____612 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____624 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____624 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____634 ->
               let op =
                 let uu____638 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____680) ->
                            Prims.strcat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____638
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option[@@deriving
                                                                show]
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string,expected_arity) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.strcat_lid, "^");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____884 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____884 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____938 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          if FStar_Util.starts_with str "dtuple"
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____1009 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____1009
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____1033 =
      let uu____1034 = FStar_Syntax_Subst.compress t  in
      uu____1034.FStar_Syntax_Syntax.n  in
    match uu____1033 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____1057 = string_to_op s  in
        (match uu____1057 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1091 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____1106 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____1114 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1118 -> true
    | uu____1119 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1126 ->
        let uu____1127 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____1127
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____1135 = may_shorten lid  in
      if uu____1135 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____1204 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____1204  in
      let uu____1205 =
        let uu____1206 = FStar_Syntax_Subst.compress t  in
        uu____1206.FStar_Syntax_Syntax.n  in
      match uu____1205 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1209 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1235 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____1235
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1238 =
              let uu____1241 = bv_as_unique_ident x  in [uu____1241]  in
            FStar_Ident.lid_of_ids uu____1238  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1244 =
              let uu____1247 = bv_as_unique_ident x  in [uu____1247]  in
            FStar_Ident.lid_of_ids uu____1244  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.strcat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____1265 =
              let uu____1266 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____1266  in
            mk1 uu____1265
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____1276 -> failwith "wrong projector format")
            else
              (let uu____1280 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____1283 =
                      let uu____1285 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____1285  in
                    let uu____1287 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____1283 <> uu____1287)
                  in
               if uu____1280
               then
                 let uu____1290 =
                   let uu____1291 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____1291  in
                 mk1 uu____1290
               else
                 (let uu____1293 =
                    let uu____1294 =
                      let uu____1305 = maybe_shorten_fv env fv  in
                      (uu____1305, [])  in
                    FStar_Parser_AST.Construct uu____1294  in
                  mk1 uu____1293))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____1323 = FStar_Options.print_universes ()  in
          if uu____1323
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____1352 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____1352  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____1375 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1382 = FStar_Syntax_Syntax.is_teff t  in
          if uu____1382
          then
            let uu____1383 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____1383
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1386 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____1395 -> ("Type", true)  in
          (match uu____1386 with
           | (nm,needs_app) ->
               let typ =
                 let uu____1399 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____1399  in
               let uu____1400 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____1400
               then
                 let uu____1401 =
                   let uu____1402 =
                     let uu____1409 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____1409, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____1402  in
                 mk1 uu____1401
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____1413) ->
          let uu____1434 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____1434 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1442 = FStar_Options.print_implicits ()  in
                 if uu____1442 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1459  ->
                         match uu____1459 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____1489 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____1489 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____1497 = FStar_Options.print_implicits ()  in
                 if uu____1497 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____1503 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____1503 FStar_List.rev  in
               let rec aux body3 uu___67_1522 =
                 match uu___67_1522 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____1538 =
            let uu____1543 =
              let uu____1544 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1544]  in
            FStar_Syntax_Subst.open_term uu____1543 phi  in
          (match uu____1538 with
           | (x1,phi1) ->
               let b =
                 let uu____1548 =
                   let uu____1551 = FStar_List.hd x1  in
                   resugar_binder' env uu____1551 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____1548  in
               let uu____1556 =
                 let uu____1557 =
                   let uu____1562 = resugar_term' env phi1  in
                   (b, uu____1562)  in
                 FStar_Parser_AST.Refine uu____1557  in
               mk1 uu____1556)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1564;
             FStar_Syntax_Syntax.vars = uu____1565;_},(e,uu____1567)::[])
          when
          (let uu____1602 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____1602) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___68_1644 =
            match uu___68_1644 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____1714 -> failwith "last of an empty list"  in
          let rec last_two uu___69_1750 =
            match uu___69_1750 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____1781::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____1858::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____1925  ->
                   match uu____1925 with
                   | (e2,qual) ->
                       let uu____1942 = resugar_term' env e2  in
                       let uu____1943 = resugar_imp qual  in
                       (uu____1942, uu____1943)) args1
               in
            let uu____1944 = resugar_term' env e1  in
            match uu____1944 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____1981  ->
                       match uu____1981 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____1997 = FStar_Options.print_implicits ()  in
            if uu____1997 then args else filter_imp args  in
          let uu____2009 = resugar_term_as_op e  in
          (match uu____2009 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____2020) ->
               (match args1 with
                | (fst1,uu____2026)::(snd1,uu____2028)::rest ->
                    let e1 =
                      let uu____2059 =
                        let uu____2060 =
                          let uu____2067 =
                            let uu____2070 = resugar_term' env fst1  in
                            let uu____2071 =
                              let uu____2074 = resugar_term' env snd1  in
                              [uu____2074]  in
                            uu____2070 :: uu____2071  in
                          ((FStar_Ident.id_of_text "*"), uu____2067)  in
                        FStar_Parser_AST.Op uu____2060  in
                      mk1 uu____2059  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun uu____2087  ->
                           match uu____2087 with
                           | (x,uu____2093) ->
                               let uu____2094 =
                                 let uu____2095 =
                                   let uu____2102 =
                                     let uu____2105 =
                                       let uu____2108 = resugar_term' env x
                                          in
                                       [uu____2108]  in
                                     e1 :: uu____2105  in
                                   ((FStar_Ident.id_of_text "*"), uu____2102)
                                    in
                                 FStar_Parser_AST.Op uu____2095  in
                               mk1 uu____2094) e1 rest
                | uu____2111 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2120) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____2146)::[] -> b
                 | uu____2163 -> failwith "wrong arguments to dtuple"  in
               let uu____2174 =
                 let uu____2175 = FStar_Syntax_Subst.compress body  in
                 uu____2175.FStar_Syntax_Syntax.n  in
               (match uu____2174 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2180) ->
                    let uu____2201 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____2201 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____2209 = FStar_Options.print_implicits ()
                              in
                           if uu____2209 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         mk1 (FStar_Parser_AST.Sum (xs3, body3)))
                | uu____2221 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2242  ->
                              match uu____2242 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____2254) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____2260) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____2265 = FStar_List.hd args1  in
               (match uu____2265 with
                | (t1,uu____2279) ->
                    let uu____2284 =
                      let uu____2285 = FStar_Syntax_Subst.compress t1  in
                      uu____2285.FStar_Syntax_Syntax.n  in
                    (match uu____2284 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____2290 =
                           let uu____2291 =
                             let uu____2296 = resugar_term' env t1  in
                             (uu____2296, f)  in
                           FStar_Parser_AST.Project uu____2291  in
                         mk1 uu____2290
                     | uu____2297 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____2298) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____2318 =
                 match new_args with
                 | (a1,uu____2336)::(a2,uu____2338)::[] -> (a1, a2)
                 | uu____2369 -> failwith "wrong arguments to try_with"  in
               (match uu____2318 with
                | (body,handler) ->
                    let decomp term =
                      let uu____2400 =
                        let uu____2401 = FStar_Syntax_Subst.compress term  in
                        uu____2401.FStar_Syntax_Syntax.n  in
                      match uu____2400 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____2406) ->
                          let uu____2427 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____2427 with | (x1,e2) -> e2)
                      | uu____2434 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____2436 = decomp body  in
                      resugar_term' env uu____2436  in
                    let handler1 =
                      let uu____2438 = decomp handler  in
                      resugar_term' env uu____2438  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____2444,uu____2445,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____2477,uu____2478,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____2515 =
                            let uu____2516 =
                              let uu____2525 = resugar_body t11  in
                              (uu____2525, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____2516  in
                          mk1 uu____2515
                      | uu____2528 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____2583 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____2613) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____2619) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____2704 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____2715 =
                   let uu____2716 = FStar_Syntax_Subst.compress body  in
                   uu____2716.FStar_Syntax_Syntax.n  in
                 match uu____2715 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____2721) ->
                     let uu____2742 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____2742 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____2750 = FStar_Options.print_implicits ()
                               in
                            if uu____2750 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____2759 =
                            let uu____2768 =
                              let uu____2769 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____2769.FStar_Syntax_Syntax.n  in
                            match uu____2768 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____2787 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____2815 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____2851  ->
                                                     match uu____2851 with
                                                     | (e2,uu____2857) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____2815, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____2865 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____2865)
                                  | uu____2872 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____2787 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____2903 ->
                                let uu____2904 = resugar_term' env body2  in
                                ([], uu____2904)
                             in
                          (match uu____2759 with
                           | (pats,body3) ->
                               let uu____2921 = uncurry xs3 pats body3  in
                               (match uu____2921 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      mk1
                                        (FStar_Parser_AST.QForall
                                           (xs5, pats1, body4))
                                    else
                                      mk1
                                        (FStar_Parser_AST.QExists
                                           (xs5, pats1, body4)))))
                 | uu____2969 ->
                     if op = "forall"
                     then
                       let uu____2970 =
                         let uu____2971 =
                           let uu____2984 = resugar_term' env body  in
                           ([], [[]], uu____2984)  in
                         FStar_Parser_AST.QForall uu____2971  in
                       mk1 uu____2970
                     else
                       (let uu____2996 =
                          let uu____2997 =
                            let uu____3010 = resugar_term' env body  in
                            ([], [[]], uu____3010)  in
                          FStar_Parser_AST.QExists uu____2997  in
                        mk1 uu____2996)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____3037)::[] -> resugar b
                  | uu____3054 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____3064) ->
               let uu____3069 = FStar_List.hd args1  in
               (match uu____3069 with
                | (e1,uu____3083) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3150  ->
                         match uu____3150 with
                         | (e1,qual) ->
                             let uu____3167 = resugar_term' env e1  in
                             let uu____3168 = resugar_imp qual  in
                             (uu____3167, uu____3168)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3181 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____3181 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____3229 =
                               let uu____3230 =
                                 let uu____3237 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____3237)  in
                               FStar_Parser_AST.Op uu____3230  in
                             mk1 uu____3229  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____3255  ->
                                  match uu____3255 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____3270 =
                      let uu____3271 =
                        let uu____3278 =
                          let uu____3281 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3281
                           in
                        (op1, uu____3278)  in
                      FStar_Parser_AST.Op uu____3271  in
                    mk1 uu____3270
                | uu____3294 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____3363 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____3363 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____3409 =
                   let uu____3422 =
                     let uu____3427 = resugar_pat' env pat1 branch_bv  in
                     let uu____3428 = resugar_term' env e  in
                     (uu____3427, uu____3428)  in
                   (FStar_Pervasives_Native.None, uu____3422)  in
                 [uu____3409]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____3480,t1)::(pat2,uu____3483,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____3579 =
            let uu____3580 =
              let uu____3587 = resugar_term' env e  in
              let uu____3588 = resugar_term' env t1  in
              let uu____3589 = resugar_term' env t2  in
              (uu____3587, uu____3588, uu____3589)  in
            FStar_Parser_AST.If uu____3580  in
          mk1 uu____3579
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____3653 =
            match uu____3653 with
            | (pat,wopt,b) ->
                let uu____3695 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____3695 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____3747 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____3747
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____3751 =
            let uu____3752 =
              let uu____3767 = resugar_term' env e  in
              let uu____3768 = FStar_List.map resugar_branch branches  in
              (uu____3767, uu____3768)  in
            FStar_Parser_AST.Match uu____3752  in
          mk1 uu____3751
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____3814) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____3881 =
            let uu____3882 =
              let uu____3891 = resugar_term' env e  in
              (uu____3891, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____3882  in
          mk1 uu____3881
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____3915 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____3915 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____3966 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____3966
                    in
                 let uu____3971 =
                   let uu____3976 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____3976
                    in
                 match uu____3971 with
                 | (univs1,td) ->
                     let uu____3995 =
                       let uu____4004 =
                         let uu____4005 = FStar_Syntax_Subst.compress td  in
                         uu____4005.FStar_Syntax_Syntax.n  in
                       match uu____4004 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4016,(t1,uu____4018)::(d,uu____4020)::[])
                           -> (t1, d)
                       | uu____4063 -> failwith "wrong let binding format"
                        in
                     (match uu____3995 with
                      | (typ,def) ->
                          let uu____4098 =
                            let uu____4105 =
                              let uu____4106 =
                                FStar_Syntax_Subst.compress def  in
                              uu____4106.FStar_Syntax_Syntax.n  in
                            match uu____4105 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____4117) ->
                                let uu____4138 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____4138 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____4152 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____4152
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____4154 -> ([], def, false)  in
                          (match uu____4098 with
                           | (binders,term,is_pat_app) ->
                               let uu____4186 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4197 =
                                       let uu____4198 =
                                         let uu____4199 =
                                           let uu____4206 =
                                             bv_as_unique_ident bv  in
                                           (uu____4206,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____4199
                                          in
                                       mk_pat uu____4198  in
                                     (uu____4197, term)
                                  in
                               (match uu____4186 with
                                | (pat,term1) ->
                                    let uu____4227 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4259  ->
                                                  match uu____4259 with
                                                  | (bv,q) ->
                                                      let uu____4274 =
                                                        resugar_arg_qual q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____4274
                                                        (fun q1  ->
                                                           let uu____4286 =
                                                             let uu____4287 =
                                                               let uu____4294
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____4294,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4287
                                                              in
                                                           mk_pat uu____4286)))
                                           in
                                        let uu____4297 =
                                          let uu____4302 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4302)
                                           in
                                        let uu____4305 =
                                          universe_to_string univs1  in
                                        (uu____4297, uu____4305)
                                      else
                                        (let uu____4311 =
                                           let uu____4316 =
                                             resugar_term' env term1  in
                                           (pat, uu____4316)  in
                                         let uu____4317 =
                                           universe_to_string univs1  in
                                         (uu____4311, uu____4317))
                                       in
                                    (attrs_opt, uu____4227))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____4415 =
                   match uu____4415 with
                   | (attrs,(pb,univs1)) ->
                       let uu____4471 =
                         let uu____4472 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____4472  in
                       if uu____4471
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____4547) ->
          let s =
            let uu____4573 =
              let uu____4574 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_All.pipe_right uu____4574 FStar_Util.string_of_int  in
            Prims.strcat "?u" uu____4573  in
          let uu____4575 = mk1 FStar_Parser_AST.Wild  in label s uu____4575
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___70_4585 =
            match uu___70_4585 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____4591,(uu____4592,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____4653 =
                        let uu____4654 =
                          let uu____4663 = resugar_seq t11  in
                          (uu____4663, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____4654  in
                      mk1 uu____4653
                  | uu____4666 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e
            | FStar_Syntax_Syntax.Mutable_alloc  ->
                let term = resugar_term' env e  in
                (match term.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Let
                     (FStar_Parser_AST.NoLetQualifier ,l,t1) ->
                     mk1
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.Mutable, l, t1))
                 | uu____4712 ->
                     failwith
                       "mutable_alloc should have let term with no qualifier")
            | FStar_Syntax_Syntax.Mutable_rval  ->
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                let uu____4714 =
                  let uu____4715 = FStar_Syntax_Subst.compress e  in
                  uu____4715.FStar_Syntax_Syntax.n  in
                (match uu____4714 with
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                          fv1;
                        FStar_Syntax_Syntax.pos = uu____4719;
                        FStar_Syntax_Syntax.vars = uu____4720;_},(term,uu____4722)::[])
                     -> resugar_term' env term
                 | uu____4755 -> failwith "mutable_rval should have app term")
             in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____4793  ->
                         match uu____4793 with
                         | (x,uu____4799) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled (l,uu____4801,p) ->
               let uu____4803 =
                 let uu____4804 =
                   let uu____4811 = resugar_term' env e  in
                   (uu____4811, l, p)  in
                 FStar_Parser_AST.Labeled uu____4804  in
               mk1 uu____4803
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               let uu____4820 =
                 let uu____4821 =
                   let uu____4830 = resugar_term' env e  in
                   let uu____4831 =
                     let uu____4832 =
                       let uu____4833 =
                         let uu____4844 =
                           let uu____4851 =
                             let uu____4856 = resugar_term' env t1  in
                             (uu____4856, FStar_Parser_AST.Nothing)  in
                           [uu____4851]  in
                         (name1, uu____4844)  in
                       FStar_Parser_AST.Construct uu____4833  in
                     mk1 uu____4832  in
                   (uu____4830, uu____4831, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4821  in
               mk1 uu____4820
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____4874,t1) ->
               let uu____4880 =
                 let uu____4881 =
                   let uu____4890 = resugar_term' env e  in
                   let uu____4891 =
                     let uu____4892 =
                       let uu____4893 =
                         let uu____4904 =
                           let uu____4911 =
                             let uu____4916 = resugar_term' env t1  in
                             (uu____4916, FStar_Parser_AST.Nothing)  in
                           [uu____4911]  in
                         (name1, uu____4904)  in
                       FStar_Parser_AST.Construct uu____4893  in
                     mk1 uu____4892  in
                   (uu____4890, uu____4891, FStar_Pervasives_Native.None)  in
                 FStar_Parser_AST.Ascribed uu____4881  in
               mk1 uu____4880
           | FStar_Syntax_Syntax.Meta_quoted (qt,qi) ->
               let uu____4939 =
                 let uu____4940 =
                   let uu____4945 = resugar_term' env qt  in
                   (uu____4945, (qi.FStar_Syntax_Syntax.qopen))  in
                 FStar_Parser_AST.Quote uu____4940  in
               mk1 uu____4939)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____4978 = FStar_Options.print_universes ()  in
               if uu____4978
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____5039 = FStar_Options.print_universes ()  in
               if uu____5039
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____5080 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____5080, FStar_Parser_AST.Nothing)  in
          let uu____5081 = FStar_Options.print_effect_args ()  in
          if uu____5081
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              if
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____5168 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____5168, (FStar_Pervasives_Native.snd post))  in
                    let uu____5177 =
                      let uu____5186 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____5186 then [] else [pre]  in
                    let uu____5216 =
                      let uu____5225 =
                        let uu____5234 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____5234 then [] else [pats]  in
                      FStar_List.append [post1] uu____5225  in
                    FStar_List.append uu____5177 uu____5216
                | uu____5288 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____5317  ->
                   match uu____5317 with
                   | (e,uu____5327) ->
                       let uu____5328 = resugar_term' env e  in
                       (uu____5328, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___71_5349 =
              match uu___71_5349 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____5382 = resugar_term' env e  in
                         (uu____5382, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____5387 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____5433 = b  in
        match uu____5433 with
        | (x,aq) ->
            let uu____5438 = resugar_arg_qual aq  in
            FStar_Util.map_opt uu____5438
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____5452 =
                       let uu____5453 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____5453  in
                     FStar_Parser_AST.mk_binder uu____5452 r
                       FStar_Parser_AST.Type_level imp
                 | uu____5454 ->
                     let uu____5455 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____5455
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____5457 =
                          let uu____5458 =
                            let uu____5463 = bv_as_unique_ident x  in
                            (uu____5463, e)  in
                          FStar_Parser_AST.Annotated uu____5458  in
                        FStar_Parser_AST.mk_binder uu____5457 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____5481 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____5481  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____5484 =
                if used
                then
                  let uu____5485 =
                    let uu____5492 = bv_as_unique_ident v1  in
                    (uu____5492, aqual)  in
                  FStar_Parser_AST.PatVar uu____5485
                else FStar_Parser_AST.PatWild  in
              mk1 uu____5484  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____5498;
                  FStar_Syntax_Syntax.vars = uu____5499;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____5513 = FStar_Options.print_bound_var_types ()  in
                if uu____5513
                then
                  let uu____5514 =
                    let uu____5515 =
                      let uu____5520 = resugar_term' env typ  in
                      (pat, uu____5520)  in
                    FStar_Parser_AST.PatAscribed uu____5515  in
                  mk1 uu____5514
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.aqual ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____5530 = resugar_arg_qual qual  in
          FStar_Util.map_opt uu____5530
            (fun aqual  ->
               let uu____5542 =
                 let uu____5547 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                   uu____5547
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____5542)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____5596 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____5596) &&
            (let uu____5598 =
               FStar_List.existsML
                 (fun uu____5609  ->
                    match uu____5609 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____5625)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____5630 -> false
                          | uu____5631 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____5598)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____5684 = may_drop_implicits args  in
            if uu____5684 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____5706  ->
                 match uu____5706 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____5752 =
                  let uu____5753 =
                    let uu____5754 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____5754  in
                  Prims.op_Negation uu____5753  in
                if uu____5752
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____5790 = filter_pattern_imp args  in
              (match uu____5790 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____5830 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____5830 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____5846 =
                       let uu____5851 =
                         let uu____5852 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____5852
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____5851)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____5846);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____5897  ->
                        match uu____5897 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____5909 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____5909)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____5913;
                 FStar_Syntax_Syntax.fv_delta = uu____5914;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____5941 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____5941 FStar_List.rev  in
              let args1 =
                let uu____5957 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____5977  ->
                          match uu____5977 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____5957 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____6047 = map21 tl1 []  in
                    (hd1, (mk1 FStar_Parser_AST.PatWild)) :: uu____6047
                | (hd1::tl1,hd2::tl2) ->
                    let uu____6070 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____6070
                 in
              let args2 =
                let uu____6088 = map21 fields1 args1  in
                FStar_All.pipe_right uu____6088 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____6130 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____6130 with
               | FStar_Pervasives_Native.Some (op,uu____6140) ->
                   mk1
                     (FStar_Parser_AST.PatOp
                        (FStar_Ident.mk_ident
                           (op,
                             ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))))
               | FStar_Pervasives_Native.None  ->
                   let uu____6157 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____6157 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____6162 ->
              mk1 FStar_Parser_AST.PatWild
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___72_6175  ->
    match uu___72_6175 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Visible
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  ->
        if true
        then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some FStar_Parser_AST.Logic
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____6184 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____6185 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____6186 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____6191 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____6200 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____6209 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___73_6212  ->
    match uu___73_6212 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts,FStar_Parser_AST.tycon)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____6242,datacons) ->
            let uu____6252 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____6279,uu____6280,uu____6281,inductive_lid,uu____6283,uu____6284)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____6289 -> failwith "unexpected"))
               in
            (match uu____6252 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____6308 = FStar_Options.print_implicits ()  in
                   if uu____6308 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____6318 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___74_6323  ->
                             match uu___74_6323 with
                             | FStar_Syntax_Syntax.RecordType uu____6324 ->
                                 true
                             | uu____6333 -> false))
                      in
                   if uu____6318
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____6381,univs1,term,uu____6384,num,uu____6386)
                           ->
                           let uu____6391 =
                             let uu____6392 =
                               FStar_Syntax_Subst.compress term  in
                             uu____6392.FStar_Syntax_Syntax.n  in
                           (match uu____6391 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____6406)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____6467  ->
                                          match uu____6467 with
                                          | (b,qual) ->
                                              let uu____6482 =
                                                let uu____6483 =
                                                  bv_as_unique_ident b  in
                                                FStar_Syntax_Util.unmangle_field_name
                                                  uu____6483
                                                 in
                                              let uu____6484 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____6482, uu____6484,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____6495 -> failwith "unexpected")
                       | uu____6506 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____6627,num,uu____6629) ->
                            let c =
                              let uu____6647 =
                                let uu____6650 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____6650  in
                              ((l.FStar_Ident.ident), uu____6647,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____6667 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____6743 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____6761 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____6761;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____6777 = ts  in
        match uu____6777 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____6785 =
              let uu____6786 =
                let uu____6799 =
                  let uu____6808 =
                    let uu____6815 =
                      let uu____6816 =
                        let uu____6829 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None, uu____6829)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____6816  in
                    (uu____6815, FStar_Pervasives_Native.None)  in
                  [uu____6808]  in
                (false, uu____6799)  in
              FStar_Parser_AST.Tycon uu____6786  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6785
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tsheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____6889 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____6889 with
              | (bs,action_defn) ->
                  let uu____6896 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____6896 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____6904 = FStar_Options.print_implicits ()
                            in
                         if uu____6904
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____6909 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____6909 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____6923 =
                             let uu____6934 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____6934,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____6923  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____7008 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____7008 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____7016 = FStar_Options.print_implicits ()  in
                  if uu____7016 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____7021 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____7021 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
                let mandatory_members_decls =
                  if for_free
                  then [repr; return_repr; bind_repr]
                  else
                    [repr;
                    return_repr;
                    bind_repr;
                    ret_wp;
                    bind_wp;
                    if_then_else1;
                    ite_wp;
                    stronger;
                    close_wp;
                    assert_p;
                    assume_p;
                    null_wp;
                    trivial]
                   in
                let actions =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                    (FStar_List.map (fun a  -> resugar_action a false))
                   in
                let decls = FStar_List.append mandatory_members_decls actions
                   in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7081) ->
          let uu____7090 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____7112 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____7129 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____7136 -> false
                    | uu____7151 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____7090 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____7183 se1 =
                 match uu____7183 with
                 | (datacon_ses1,tycons) ->
                     let uu____7209 = resugar_typ env datacon_ses1 se1  in
                     (match uu____7209 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____7224 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____7224 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____7259 =
                           let uu____7260 =
                             let uu____7261 =
                               let uu____7274 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, uu____7274)  in
                             FStar_Parser_AST.Tycon uu____7261  in
                           decl'_to_decl se uu____7260  in
                         FStar_Pervasives_Native.Some uu____7259
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____7305,uu____7306,uu____7307,uu____7308,uu____7309)
                              ->
                              let uu____7314 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____7314
                          | uu____7317 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____7320 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____7326) ->
          let uu____7331 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___75_7337  ->
                    match uu___75_7337 with
                    | FStar_Syntax_Syntax.Projector (uu____7338,uu____7339)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7340 -> true
                    | uu____7341 -> false))
             in
          if uu____7331
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____7364) ->
                 let uu____7393 =
                   let uu____7394 =
                     let uu____7395 =
                       let uu____7406 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____7406)  in
                     FStar_Parser_AST.TopLevelLet uu____7395  in
                   decl'_to_decl se uu____7394  in
                 FStar_Pervasives_Native.Some uu____7393
             | uu____7443 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____7447,fml) ->
          let uu____7449 =
            let uu____7450 =
              let uu____7451 =
                let uu____7456 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____7456)  in
              FStar_Parser_AST.Assume uu____7451  in
            decl'_to_decl se uu____7450  in
          FStar_Pervasives_Native.Some uu____7449
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____7458 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7458
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____7460 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____7460
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____7469,t) ->
                let uu____7481 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7481
            | uu____7482 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____7490,t) ->
                let uu____7502 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____7502
            | uu____7503 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____7527 -> failwith "Should not happen hopefully"  in
          let uu____7536 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____7536
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags1) ->
          let uu____7546 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____7546 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____7556 = FStar_Options.print_implicits ()  in
                 if uu____7556 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____7565 =
                 let uu____7566 =
                   let uu____7567 =
                     let uu____7580 =
                       let uu____7589 =
                         let uu____7596 =
                           let uu____7597 =
                             let uu____7610 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____7610)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____7597  in
                         (uu____7596, FStar_Pervasives_Native.None)  in
                       [uu____7589]  in
                     (false, uu____7580)  in
                   FStar_Parser_AST.Tycon uu____7567  in
                 decl'_to_decl se uu____7566  in
               FStar_Pervasives_Native.Some uu____7565)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____7638 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____7638
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____7642 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___76_7648  ->
                    match uu___76_7648 with
                    | FStar_Syntax_Syntax.Projector (uu____7649,uu____7650)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____7651 -> true
                    | uu____7652 -> false))
             in
          if uu____7642
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____7657 =
                 (let uu____7660 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____7660) || (FStar_List.isEmpty uvs)
                  in
               if uu____7657
               then resugar_term' env t
               else
                 (let uu____7662 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____7662 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____7670 = resugar_term' env t1  in
                      label universes uu____7670)
                in
             let uu____7671 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____7671)
      | FStar_Syntax_Syntax.Sig_splice t ->
          let uu____7673 =
            let uu____7674 =
              let uu____7675 = resugar_term' env t  in
              FStar_Parser_AST.Splice uu____7675  in
            decl'_to_decl se uu____7674  in
          FStar_Pervasives_Native.Some uu____7673
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7676 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____7693 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____7708 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) = FStar_Syntax_DsEnv.empty_env () 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____7724 = noenv resugar_term'  in uu____7724 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____7736 = noenv resugar_sigelt'  in uu____7736 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____7748 = noenv resugar_comp'  in uu____7748 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____7763 = noenv resugar_pat'  in uu____7763 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____7786 = noenv resugar_binder'  in uu____7786 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____7802 = noenv resugar_tscheme'  in uu____7802 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____7823 = noenv resugar_eff_decl'  in
          uu____7823 for_free r q ed
  