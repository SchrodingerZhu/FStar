open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____37 'Auu____38 .
    Prims.bool -> ('Auu____37 -> 'Auu____38) -> 'Auu____37 -> 'Auu____38
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let (str : Prims.string -> FStar_Pprint.document) =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____135 'Auu____136 .
    'Auu____135 ->
      ('Auu____136 -> 'Auu____135) ->
        'Auu____136 FStar_Pervasives_Native.option -> 'Auu____135
  =
  fun n1  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
  
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let (break1 : FStar_Pprint.document) =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map :
  'Auu____230 .
    FStar_Pprint.document ->
      ('Auu____230 -> FStar_Pprint.document) ->
        'Auu____230 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____255 =
          let uu____256 =
            let uu____257 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____257  in
          FStar_Pprint.separate_map uu____256 f l  in
        FStar_Pprint.group uu____255
  
let precede_break_separate_map :
  'Auu____268 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____268 -> FStar_Pprint.document) ->
          'Auu____268 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____298 =
            let uu____299 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____300 =
              let uu____301 = FStar_List.hd l  in
              FStar_All.pipe_right uu____301 f  in
            FStar_Pprint.precede uu____299 uu____300  in
          let uu____302 =
            let uu____303 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____309 =
                   let uu____310 =
                     let uu____311 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____311  in
                   FStar_Pprint.op_Hat_Hat sep uu____310  in
                 FStar_Pprint.op_Hat_Hat break1 uu____309) uu____303
             in
          FStar_Pprint.op_Hat_Hat uu____298 uu____302
  
let concat_break_map :
  'Auu____318 .
    ('Auu____318 -> FStar_Pprint.document) ->
      'Auu____318 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____338 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____342 = f x  in FStar_Pprint.op_Hat_Hat uu____342 break1)
          l
         in
      FStar_Pprint.group uu____338
  
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    let uu____383 = str "begin"  in
    let uu____384 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____383 contents uu____384
  
let separate_map_last :
  'Auu____393 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____393 -> FStar_Pprint.document) ->
        'Auu____393 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.separate sep es1
  
let separate_break_map_last :
  'Auu____445 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____445 -> FStar_Pprint.document) ->
        'Auu____445 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____475 =
          let uu____476 =
            let uu____477 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____477  in
          separate_map_last uu____476 f l  in
        FStar_Pprint.group uu____475
  
let separate_map_or_flow :
  'Auu____486 .
    FStar_Pprint.document ->
      ('Auu____486 -> FStar_Pprint.document) ->
        'Auu____486 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____520 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____520 -> FStar_Pprint.document) ->
        'Auu____520 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.flow sep es1
  
let separate_map_or_flow_last :
  'Auu____572 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____572 -> FStar_Pprint.document) ->
        'Auu____572 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep  -> fun l  -> separate_map_or_flow sep FStar_Pervasives.id l 
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n1  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____642 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____642
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____662 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____662 -> FStar_Pprint.document) ->
                  'Auu____662 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____715 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____715
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____734 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____734 -> FStar_Pprint.document) ->
                  'Auu____734 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____787 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____787
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____802  ->
    match uu____802 with
    | (comment,keywords) ->
        let uu____827 =
          let uu____828 =
            let uu____831 = str comment  in
            let uu____832 =
              let uu____835 =
                let uu____838 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____847  ->
                       match uu____847 with
                       | (k,v1) ->
                           let uu____854 =
                             let uu____857 = str k  in
                             let uu____858 =
                               let uu____861 =
                                 let uu____864 = str v1  in [uu____864]  in
                               FStar_Pprint.rarrow :: uu____861  in
                             uu____857 :: uu____858  in
                           FStar_Pprint.concat uu____854) keywords
                   in
                [uu____838]  in
              FStar_Pprint.space :: uu____835  in
            uu____831 :: uu____832  in
          FStar_Pprint.concat uu____828  in
        FStar_Pprint.group uu____827
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____870 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____882 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____882
      | uu____883 -> false
  
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid' 
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid' 
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____925::(e2,uu____927)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____950 -> false  in
      aux
  
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu____968,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____979,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____1000 = extract_from_list e2  in e1 :: uu____1000
    | uu____1003 ->
        let uu____1004 =
          let uu____1005 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1005  in
        failwith uu____1004
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1014;
           FStar_Parser_AST.level = uu____1015;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1017 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1025;
           FStar_Parser_AST.level = uu____1026;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1028;
                                                         FStar_Parser_AST.level
                                                           = uu____1029;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1031;
                                                    FStar_Parser_AST.level =
                                                      uu____1032;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.set_singleton)
          &&
          (FStar_Ident.lid_equals maybe_addr_of_lid
             FStar_Parser_Const.heap_addr_of_lid)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____1034;
                FStar_Parser_AST.level = uu____1035;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1037;
           FStar_Parser_AST.level = uu____1038;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1040 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1050 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1051;
           FStar_Parser_AST.range = uu____1052;
           FStar_Parser_AST.level = uu____1053;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1054;
                                                         FStar_Parser_AST.range
                                                           = uu____1055;
                                                         FStar_Parser_AST.level
                                                           = uu____1056;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1058;
                                                    FStar_Parser_AST.level =
                                                      uu____1059;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1060;
                FStar_Parser_AST.range = uu____1061;
                FStar_Parser_AST.level = uu____1062;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1064;
           FStar_Parser_AST.level = uu____1065;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1067 = extract_from_ref_set e1  in
        let uu____1070 = extract_from_ref_set e2  in
        FStar_List.append uu____1067 uu____1070
    | uu____1073 ->
        let uu____1074 =
          let uu____1075 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1075  in
        failwith uu____1074
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1083 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1083
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1089 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1089
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1097 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1097 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1105 = FStar_Ident.text_of_id op  in uu____1105 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1171 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1187 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1193 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1199 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___104_1220  ->
    match uu___104_1220 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___105_1245  ->
      match uu___105_1245 with
      | FStar_Util.Inl c ->
          let uu____1254 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1254 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1265 .
    Prims.string ->
      ('Auu____1265,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1286  ->
      match uu____1286 with
      | (assoc_levels,tokens) ->
          let uu____1314 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1314 <> FStar_Pervasives_Native.None
  
let (opinfix4 : associativity_level) = (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 : associativity_level) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 : associativity_level) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl : associativity_level) = (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 : associativity_level) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right : associativity_level) = (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d : associativity_level) = (Left, [FStar_Util.Inl 36]) 
let (opinfix0c : associativity_level) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : associativity_level) = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b : associativity_level) = (Left, [FStar_Util.Inl 38]) 
let (opinfix0a : associativity_level) = (Left, [FStar_Util.Inl 124]) 
let (colon_equals : associativity_level) = (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : associativity_level) = (Right, [FStar_Util.Inr "&"]) 
let (colon_colon : associativity_level) = (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec : associativity_level Prims.list) =
  [opinfix4;
  opinfix3;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon] 
let (level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,token
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___106_1432 =
    match uu___106_1432 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1462  ->
         match uu____1462 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1521 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1521 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1561) ->
          assoc_levels
      | uu____1590 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1626 .
    ('Auu____1626,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1671 =
        FStar_List.tryFind
          (fun uu____1701  ->
             match uu____1701 with
             | (uu____1714,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1671 with
      | FStar_Pervasives_Native.Some ((uu____1736,l1,uu____1738),uu____1739)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1774 =
            let uu____1775 =
              let uu____1776 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1776  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1775
             in
          failwith uu____1774
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1798 = assign_levels level_associativity_spec op  in
    match uu____1798 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1828 =
      let uu____1831 =
        let uu____1836 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1836  in
      FStar_List.tryFind uu____1831 operatorInfix0ad12  in
    uu____1828 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1894 =
      let uu____1908 =
        let uu____1924 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1924  in
      FStar_List.tryFind uu____1908 opinfix34  in
    uu____1894 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1980 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1980
    then (Prims.parse_int "1")
    else
      (let uu____1982 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1982
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____1991 . FStar_Ident.ident -> 'Auu____1991 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2007 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2007 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2009 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2009
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2010 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2010 [".()<-"; ".[]<-"]
      | uu____2011 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2049 .
    ('Auu____2049 -> FStar_Pprint.document) ->
      'Auu____2049 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2090 = FStar_ST.op_Bang comment_stack  in
          match uu____2090 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2149 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2149
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2186 =
                    let uu____2187 =
                      let uu____2188 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2188
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2187  in
                  comments_before_pos uu____2186 print_pos lookahead_pos))
              else
                (let uu____2190 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2190))
           in
        let uu____2191 =
          let uu____2196 =
            let uu____2197 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2197  in
          let uu____2198 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2196 uu____2198  in
        match uu____2191 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2204 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2204
              else comments  in
            let uu____2210 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2210
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2231 = FStar_ST.op_Bang comment_stack  in
          match uu____2231 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2315 =
                    let uu____2316 =
                      let uu____2317 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2317  in
                    uu____2316 - lbegin  in
                  max k uu____2315  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2320 =
                    let uu____2321 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2322 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2321 uu____2322  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2320  in
                let uu____2323 =
                  let uu____2324 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2324  in
                place_comments_until_pos (Prims.parse_int "1") uu____2323
                  pos_end doc2))
          | uu____2325 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2334 =
                     let uu____2335 = FStar_Range.line_of_pos pos_end  in
                     uu____2335 - lbegin  in
                   max (Prims.parse_int "1") uu____2334  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2337 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2337)
  
let separate_map_with_comments :
  'Auu____2350 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2350 -> FStar_Pprint.document) ->
          'Auu____2350 Prims.list ->
            ('Auu____2350 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2407 x =
              match uu____2407 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2421 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2421 doc1
                     in
                  let uu____2422 =
                    let uu____2423 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2423  in
                  let uu____2424 =
                    let uu____2425 =
                      let uu____2426 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2426  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2425  in
                  (uu____2422, uu____2424)
               in
            let uu____2427 =
              let uu____2434 = FStar_List.hd xs  in
              let uu____2435 = FStar_List.tl xs  in (uu____2434, uu____2435)
               in
            match uu____2427 with
            | (x,xs1) ->
                let init1 =
                  let uu____2451 =
                    let uu____2452 =
                      let uu____2453 = extract_range x  in
                      FStar_Range.end_of_range uu____2453  in
                    FStar_Range.line_of_pos uu____2452  in
                  let uu____2454 =
                    let uu____2455 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2455  in
                  (uu____2451, uu____2454)  in
                let uu____2456 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2456
  
let separate_map_with_comments_kw :
  'Auu____2479 'Auu____2480 .
    'Auu____2479 ->
      'Auu____2479 ->
        ('Auu____2479 -> 'Auu____2480 -> FStar_Pprint.document) ->
          'Auu____2480 Prims.list ->
            ('Auu____2480 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2542 x =
              match uu____2542 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2556 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2556 doc1
                     in
                  let uu____2557 =
                    let uu____2558 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2558  in
                  let uu____2559 =
                    let uu____2560 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2560  in
                  (uu____2557, uu____2559)
               in
            let uu____2561 =
              let uu____2568 = FStar_List.hd xs  in
              let uu____2569 = FStar_List.tl xs  in (uu____2568, uu____2569)
               in
            match uu____2561 with
            | (x,xs1) ->
                let init1 =
                  let uu____2585 =
                    let uu____2586 =
                      let uu____2587 = extract_range x  in
                      FStar_Range.end_of_range uu____2587  in
                    FStar_Range.line_of_pos uu____2586  in
                  let uu____2588 = f prefix1 x  in (uu____2585, uu____2588)
                   in
                let uu____2589 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2589
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3299)) ->
          let uu____3302 =
            let uu____3303 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3303 FStar_Util.is_upper  in
          if uu____3302
          then
            let uu____3306 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3306 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3308 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3315 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3316 =
      let uu____3317 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3318 =
        let uu____3319 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3319  in
      FStar_Pprint.op_Hat_Hat uu____3317 uu____3318  in
    FStar_Pprint.op_Hat_Hat uu____3315 uu____3316

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3321 ->
        let uu____3322 =
          let uu____3323 = str "@ "  in
          let uu____3324 =
            let uu____3325 =
              let uu____3326 =
                let uu____3327 =
                  let uu____3328 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3328  in
                FStar_Pprint.op_Hat_Hat uu____3327 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3326  in
            FStar_Pprint.op_Hat_Hat uu____3325 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3323 uu____3324  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3322

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3331  ->
    match uu____3331 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3367 =
                match uu____3367 with
                | (kwd,arg) ->
                    let uu____3374 = str "@"  in
                    let uu____3375 =
                      let uu____3376 = str kwd  in
                      let uu____3377 =
                        let uu____3378 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3378
                         in
                      FStar_Pprint.op_Hat_Hat uu____3376 uu____3377  in
                    FStar_Pprint.op_Hat_Hat uu____3374 uu____3375
                 in
              let uu____3379 =
                let uu____3380 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3380 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3379
           in
        let uu____3385 =
          let uu____3386 =
            let uu____3387 =
              let uu____3388 =
                let uu____3389 = str doc1  in
                let uu____3390 =
                  let uu____3391 =
                    let uu____3392 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3392  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3391  in
                FStar_Pprint.op_Hat_Hat uu____3389 uu____3390  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3388  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3387  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3386  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3385

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3396 =
          let uu____3397 = str "val"  in
          let uu____3398 =
            let uu____3399 =
              let uu____3400 = p_lident lid  in
              let uu____3401 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3400 uu____3401  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3399  in
          FStar_Pprint.op_Hat_Hat uu____3397 uu____3398  in
        let uu____3402 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3396 uu____3402
    | FStar_Parser_AST.TopLevelLet (uu____3403,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3428 =
               let uu____3429 = str "let"  in p_letlhs uu____3429 lb  in
             FStar_Pprint.group uu____3428) lbs
    | uu____3430 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___107_3445 =
          match uu___107_3445 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3453 = f x  in
              let uu____3454 =
                let uu____3455 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3455  in
              FStar_Pprint.op_Hat_Hat uu____3453 uu____3454
           in
        let uu____3456 = str "["  in
        let uu____3457 =
          let uu____3458 = p_list' l  in
          let uu____3459 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3458 uu____3459  in
        FStar_Pprint.op_Hat_Hat uu____3456 uu____3457

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3462 =
          let uu____3463 = str "open"  in
          let uu____3464 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3463 uu____3464  in
        FStar_Pprint.group uu____3462
    | FStar_Parser_AST.Include uid ->
        let uu____3466 =
          let uu____3467 = str "include"  in
          let uu____3468 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3467 uu____3468  in
        FStar_Pprint.group uu____3466
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3471 =
          let uu____3472 = str "module"  in
          let uu____3473 =
            let uu____3474 =
              let uu____3475 = p_uident uid1  in
              let uu____3476 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3475 uu____3476  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3474  in
          FStar_Pprint.op_Hat_Hat uu____3472 uu____3473  in
        let uu____3477 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3471 uu____3477
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3479 =
          let uu____3480 = str "module"  in
          let uu____3481 =
            let uu____3482 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3482  in
          FStar_Pprint.op_Hat_Hat uu____3480 uu____3481  in
        FStar_Pprint.group uu____3479
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3483,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3516 = str "effect"  in
          let uu____3517 =
            let uu____3518 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3518  in
          FStar_Pprint.op_Hat_Hat uu____3516 uu____3517  in
        let uu____3519 =
          let uu____3520 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3520 FStar_Pprint.equals
           in
        let uu____3521 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3519 uu____3521
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3542 =
          let uu____3543 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3543  in
        let uu____3556 =
          let uu____3557 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3595 =
                    let uu____3596 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3596 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3595)) uu____3557
           in
        FStar_Pprint.op_Hat_Hat uu____3542 uu____3556
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3612 = str "let"  in
          let uu____3613 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3612 uu____3613  in
        let uu____3614 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3614 p_letbinding lbs
          (fun uu____3622  ->
             match uu____3622 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3631 = str "val"  in
        let uu____3632 =
          let uu____3633 =
            let uu____3634 = p_lident lid  in
            let uu____3635 =
              let uu____3636 =
                let uu____3637 =
                  let uu____3638 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3638  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3637  in
              FStar_Pprint.group uu____3636  in
            FStar_Pprint.op_Hat_Hat uu____3634 uu____3635  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3633  in
        FStar_Pprint.op_Hat_Hat uu____3631 uu____3632
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3642 =
            let uu____3643 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3643 FStar_Util.is_upper  in
          if uu____3642
          then FStar_Pprint.empty
          else
            (let uu____3647 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3647 FStar_Pprint.space)
           in
        let uu____3648 =
          let uu____3649 = p_ident id1  in
          let uu____3650 =
            let uu____3651 =
              let uu____3652 =
                let uu____3653 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3653  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3652  in
            FStar_Pprint.group uu____3651  in
          FStar_Pprint.op_Hat_Hat uu____3649 uu____3650  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3648
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3660 = str "exception"  in
        let uu____3661 =
          let uu____3662 =
            let uu____3663 = p_uident uid  in
            let uu____3664 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3668 =
                     let uu____3669 = str "of"  in
                     let uu____3670 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3669 uu____3670  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3668) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3663 uu____3664  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3662  in
        FStar_Pprint.op_Hat_Hat uu____3660 uu____3661
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3672 = str "new_effect"  in
        let uu____3673 =
          let uu____3674 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3674  in
        FStar_Pprint.op_Hat_Hat uu____3672 uu____3673
    | FStar_Parser_AST.SubEffect se ->
        let uu____3676 = str "sub_effect"  in
        let uu____3677 =
          let uu____3678 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3678  in
        FStar_Pprint.op_Hat_Hat uu____3676 uu____3677
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3681 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3681 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3682 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3683,uu____3684) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3707 = str "%splice"  in
        let uu____3708 =
          let uu____3709 =
            let uu____3710 = str ";"  in p_list p_uident uu____3710 ids  in
          let uu____3711 =
            let uu____3712 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3712  in
          FStar_Pprint.op_Hat_Hat uu____3709 uu____3711  in
        FStar_Pprint.op_Hat_Hat uu____3707 uu____3708

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___108_3713  ->
    match uu___108_3713 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3715 = str "#set-options"  in
        let uu____3716 =
          let uu____3717 =
            let uu____3718 = str s  in FStar_Pprint.dquotes uu____3718  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3717  in
        FStar_Pprint.op_Hat_Hat uu____3715 uu____3716
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3722 = str "#reset-options"  in
        let uu____3723 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3727 =
                 let uu____3728 = str s  in FStar_Pprint.dquotes uu____3728
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3727) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3722 uu____3723
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3732 = str "#push-options"  in
        let uu____3733 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3737 =
                 let uu____3738 = str s  in FStar_Pprint.dquotes uu____3738
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3737) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3732 uu____3733
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____3763  ->
      match uu____3763 with
      | (typedecl,fsdoc_opt) ->
          let uu____3776 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3776 with
           | (decl,body) ->
               let uu____3794 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3794)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___109_3796  ->
      match uu___109_3796 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3826 = FStar_Pprint.empty  in
          let uu____3827 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3827, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3848 =
            let uu____3849 = p_typ false false t  in jump2 uu____3849  in
          let uu____3850 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3850, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3904 =
            match uu____3904 with
            | (lid1,t,doc_opt) ->
                let uu____3920 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3920
             in
          let p_fields uu____3936 =
            let uu____3937 =
              let uu____3938 =
                let uu____3939 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3939 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3938  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3937  in
          let uu____3948 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3948, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4009 =
            match uu____4009 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4035 =
                    let uu____4036 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4036  in
                  FStar_Range.extend_to_end_of_line uu____4035  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4062 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4075 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4075,
            ((fun uu____4081  ->
                let uu____4082 = datacon_doc ()  in jump2 uu____4082)))

and (p_typeDeclPrefix :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____4083  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4083 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4117 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4117  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4119 =
                        let uu____4122 =
                          let uu____4125 = p_fsdoc fsdoc  in
                          let uu____4126 =
                            let uu____4129 = cont lid_doc  in [uu____4129]
                             in
                          uu____4125 :: uu____4126  in
                        kw :: uu____4122  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4119
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4134 =
                        let uu____4135 =
                          let uu____4136 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4136 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4135
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4134
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4151 =
                          let uu____4152 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4152  in
                        prefix2 uu____4151 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4154  ->
      match uu____4154 with
      | (lid,t,doc_opt) ->
          let uu____4170 =
            let uu____4171 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4172 =
              let uu____4173 = p_lident lid  in
              let uu____4174 =
                let uu____4175 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4175  in
              FStar_Pprint.op_Hat_Hat uu____4173 uu____4174  in
            FStar_Pprint.op_Hat_Hat uu____4171 uu____4172  in
          FStar_Pprint.group uu____4170

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4176  ->
    match uu____4176 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4204 =
            let uu____4205 =
              let uu____4206 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4206  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4205  in
          FStar_Pprint.group uu____4204  in
        let uu____4207 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4208 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4212 =
                 let uu____4213 =
                   let uu____4214 =
                     let uu____4215 =
                       let uu____4216 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4216
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4215  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4214  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4213  in
               FStar_Pprint.group uu____4212) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4207 uu____4208

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4218  ->
      match uu____4218 with
      | (pat,uu____4224) ->
          let uu____4225 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4244 =
                  let uu____4245 =
                    let uu____4246 =
                      let uu____4247 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4247
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4246  in
                  FStar_Pprint.group uu____4245  in
                (pat1, uu____4244)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4259 =
                  let uu____4260 =
                    let uu____4261 =
                      let uu____4262 =
                        let uu____4263 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4263
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4262
                       in
                    FStar_Pprint.group uu____4261  in
                  let uu____4264 =
                    let uu____4265 =
                      let uu____4266 = str "by"  in
                      let uu____4267 =
                        let uu____4268 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4268
                         in
                      FStar_Pprint.op_Hat_Hat uu____4266 uu____4267  in
                    FStar_Pprint.group uu____4265  in
                  FStar_Pprint.op_Hat_Hat uu____4260 uu____4264  in
                (pat1, uu____4259)
            | uu____4269 -> (pat, FStar_Pprint.empty)  in
          (match uu____4225 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4273);
                       FStar_Parser_AST.prange = uu____4274;_},pats)
                    ->
                    let uu____4284 =
                      let uu____4285 =
                        let uu____4286 =
                          let uu____4287 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4287  in
                        FStar_Pprint.group uu____4286  in
                      let uu____4288 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4285 uu____4288  in
                    prefix2_nonempty uu____4284 ascr_doc
                | uu____4289 ->
                    let uu____4290 =
                      let uu____4291 =
                        let uu____4292 =
                          let uu____4293 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4293  in
                        FStar_Pprint.group uu____4292  in
                      FStar_Pprint.op_Hat_Hat uu____4291 ascr_doc  in
                    FStar_Pprint.group uu____4290))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4295  ->
      match uu____4295 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4304 =
            let uu____4305 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4305  in
          let uu____4306 =
            let uu____4307 =
              let uu____4308 =
                let uu____4309 =
                  let uu____4310 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4310  in
                FStar_Pprint.group uu____4309  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4308  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4307  in
          FStar_Pprint.ifflat uu____4304 uu____4306

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___110_4311  ->
    match uu___110_4311 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and (p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____4336 = p_uident uid  in
        let uu____4337 = p_binders true bs  in
        let uu____4338 =
          let uu____4339 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4339  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4336 uu____4337 uu____4338

and (p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let binders = p_binders true bs  in
          let uu____4349 =
            let uu____4350 =
              let uu____4351 =
                let uu____4352 = p_uident uid  in
                let uu____4353 = p_binders true bs  in
                let uu____4354 =
                  let uu____4355 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4355  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4352 uu____4353 uu____4354
                 in
              FStar_Pprint.group uu____4351  in
            let uu____4356 =
              let uu____4357 = str "with"  in
              let uu____4358 =
                let uu____4359 =
                  let uu____4360 =
                    let uu____4361 =
                      let uu____4362 =
                        let uu____4363 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4363
                         in
                      separate_map_last uu____4362 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4361  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4360  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4359  in
              FStar_Pprint.op_Hat_Hat uu____4357 uu____4358  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4350 uu____4356  in
          braces_with_nesting uu____4349

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4366,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4395 =
            let uu____4396 = p_lident lid  in
            let uu____4397 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4396 uu____4397  in
          let uu____4398 = p_simpleTerm ps false e  in
          prefix2 uu____4395 uu____4398
      | uu____4399 ->
          let uu____4400 =
            let uu____4401 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4401
             in
          failwith uu____4400

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4463 =
        match uu____4463 with
        | (kwd,t) ->
            let uu____4470 =
              let uu____4471 = str kwd  in
              let uu____4472 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4471 uu____4472  in
            let uu____4473 = p_simpleTerm ps false t  in
            prefix2 uu____4470 uu____4473
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4478 =
      let uu____4479 =
        let uu____4480 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4481 =
          let uu____4482 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4482  in
        FStar_Pprint.op_Hat_Hat uu____4480 uu____4481  in
      let uu____4483 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4479 uu____4483  in
    let uu____4484 =
      let uu____4485 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4485  in
    FStar_Pprint.op_Hat_Hat uu____4478 uu____4484

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___111_4486  ->
    match uu___111_4486 with
    | FStar_Parser_AST.Private  -> str "private"
    | FStar_Parser_AST.Abstract  -> str "abstract"
    | FStar_Parser_AST.Noeq  -> str "noeq"
    | FStar_Parser_AST.Unopteq  -> str "unopteq"
    | FStar_Parser_AST.Assumption  -> str "assume"
    | FStar_Parser_AST.DefaultEffect  -> str "default"
    | FStar_Parser_AST.TotalEffect  -> str "total"
    | FStar_Parser_AST.Effect_qual  -> FStar_Pprint.empty
    | FStar_Parser_AST.New  -> str "new"
    | FStar_Parser_AST.Inline  -> str "inline"
    | FStar_Parser_AST.Visible  -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen  -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction  -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible  -> str "irreducible"
    | FStar_Parser_AST.NoExtract  -> str "noextract"
    | FStar_Parser_AST.Reifiable  -> str "reifiable"
    | FStar_Parser_AST.Reflectable  -> str "reflectable"
    | FStar_Parser_AST.Opaque  -> str "opaque"
    | FStar_Parser_AST.Logic  -> str "logic"

and (p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document) =
  fun qs  ->
    match qs with
    | [] -> FStar_Pprint.empty
    | uu____4488 ->
        let uu____4489 =
          let uu____4490 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4490  in
        FStar_Pprint.op_Hat_Hat uu____4489 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___112_4493  ->
    match uu___112_4493 with
    | FStar_Parser_AST.Rec  ->
        let uu____4494 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4494
    | FStar_Parser_AST.Mutable  ->
        let uu____4495 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4495
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___113_4496  ->
    match uu___113_4496 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4498 = str "#["  in
        let uu____4499 =
          let uu____4500 = p_term false false t  in
          let uu____4501 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4500 uu____4501  in
        FStar_Pprint.op_Hat_Hat uu____4498 uu____4499

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4506 =
          let uu____4507 =
            let uu____4508 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4508  in
          FStar_Pprint.separate_map uu____4507 p_tuplePattern pats  in
        FStar_Pprint.group uu____4506
    | uu____4509 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4516 =
          let uu____4517 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4517 p_constructorPattern pats  in
        FStar_Pprint.group uu____4516
    | uu____4518 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4521;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4526 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4527 = p_constructorPattern hd1  in
        let uu____4528 = p_constructorPattern tl1  in
        infix0 uu____4526 uu____4527 uu____4528
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4530;_},pats)
        ->
        let uu____4536 = p_quident uid  in
        let uu____4537 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4536 uu____4537
    | uu____4538 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4554;
               FStar_Parser_AST.blevel = uu____4555;
               FStar_Parser_AST.aqual = uu____4556;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4564 =
               let uu____4565 = p_ident lid  in
               p_refinement aqual uu____4565 t1 phi  in
             soft_parens_with_nesting uu____4564
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4568;
               FStar_Parser_AST.blevel = uu____4569;
               FStar_Parser_AST.aqual = uu____4570;_},phi))
             ->
             let uu____4576 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4576
         | uu____4577 ->
             let uu____4582 =
               let uu____4583 = p_tuplePattern pat  in
               let uu____4584 =
                 let uu____4585 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4585
                  in
               FStar_Pprint.op_Hat_Hat uu____4583 uu____4584  in
             soft_parens_with_nesting uu____4582)
    | FStar_Parser_AST.PatList pats ->
        let uu____4589 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4589 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4606 =
          match uu____4606 with
          | (lid,pat) ->
              let uu____4613 = p_qlident lid  in
              let uu____4614 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4613 uu____4614
           in
        let uu____4615 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4615
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4625 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4626 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4627 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4625 uu____4626 uu____4627
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4636 =
          let uu____4637 =
            let uu____4638 =
              let uu____4639 = FStar_Ident.text_of_id op  in str uu____4639
               in
            let uu____4640 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4638 uu____4640  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4637  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4636
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4644 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4644 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4652 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4653 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4652 uu____4653
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4655 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4658;
           FStar_Parser_AST.prange = uu____4659;_},uu____4660)
        ->
        let uu____4665 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4665
    | FStar_Parser_AST.PatTuple (uu____4666,false ) ->
        let uu____4671 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4671
    | uu____4672 ->
        let uu____4673 =
          let uu____4674 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4674  in
        failwith uu____4673

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4676;_},uu____4677)
        -> true
    | uu____4682 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4686 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4687 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4686 uu____4687
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4694;
                   FStar_Parser_AST.blevel = uu____4695;
                   FStar_Parser_AST.aqual = uu____4696;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4700 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4700 t1 phi
            | uu____4701 ->
                let t' =
                  let uu____4703 = is_typ_tuple t  in
                  if uu____4703
                  then
                    let uu____4704 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4704
                  else p_tmFormula t  in
                let uu____4706 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4707 =
                  let uu____4708 = p_lident lid  in
                  let uu____4709 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4708 uu____4709  in
                FStar_Pprint.op_Hat_Hat uu____4706 uu____4707
             in
          if is_atomic
          then
            let uu____4710 =
              let uu____4711 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4711  in
            FStar_Pprint.group uu____4710
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4713 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4720;
                  FStar_Parser_AST.blevel = uu____4721;
                  FStar_Parser_AST.aqual = uu____4722;_},phi)
               ->
               if is_atomic
               then
                 let uu____4726 =
                   let uu____4727 =
                     let uu____4728 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4728 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4727  in
                 FStar_Pprint.group uu____4726
               else
                 (let uu____4730 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4730)
           | uu____4731 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____4740 -> false
            | FStar_Parser_AST.App uu____4751 -> false
            | FStar_Parser_AST.Op uu____4758 -> false
            | uu____4765 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4769 =
            let uu____4770 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4771 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4770 uu____4771  in
          let uu____4772 =
            let uu____4773 = p_appTerm t  in
            let uu____4774 =
              let uu____4775 =
                let uu____4776 =
                  let uu____4777 = soft_braces_with_nesting_tight phi1  in
                  let uu____4778 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4777 uu____4778  in
                FStar_Pprint.group uu____4776  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4775
               in
            FStar_Pprint.op_Hat_Hat uu____4773 uu____4774  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4769 uu____4772

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4789 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4789

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4794 = FStar_Ident.text_of_id lid  in str uu____4794)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4797 = FStar_Ident.text_of_lid lid  in str uu____4797)

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b  -> if b then soft_parens_with_nesting else (fun x  -> x)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____4815 =
              let uu____4816 =
                let uu____4817 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4817 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4816  in
            let uu____4818 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4815 uu____4818
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4822 =
              let uu____4823 =
                let uu____4824 =
                  let uu____4825 = p_lident x  in
                  let uu____4826 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4825 uu____4826  in
                let uu____4827 =
                  let uu____4828 = p_noSeqTerm true false e1  in
                  let uu____4829 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4828 uu____4829  in
                op_Hat_Slash_Plus_Hat uu____4824 uu____4827  in
              FStar_Pprint.group uu____4823  in
            let uu____4830 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4822 uu____4830
        | uu____4831 ->
            let uu____4832 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4832

and (p_noSeqTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____4843 =
              let uu____4844 = p_tmIff e1  in
              let uu____4845 =
                let uu____4846 =
                  let uu____4847 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4847
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4846  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4844 uu____4845  in
            FStar_Pprint.group uu____4843
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4853 =
              let uu____4854 = p_tmIff e1  in
              let uu____4855 =
                let uu____4856 =
                  let uu____4857 =
                    let uu____4858 = p_typ false false t  in
                    let uu____4859 =
                      let uu____4860 = str "by"  in
                      let uu____4861 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4860 uu____4861  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4858 uu____4859  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4857
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4856  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4854 uu____4855  in
            FStar_Pprint.group uu____4853
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4862;_},e1::e2::e3::[])
            ->
            let uu____4868 =
              let uu____4869 =
                let uu____4870 =
                  let uu____4871 = p_atomicTermNotQUident e1  in
                  let uu____4872 =
                    let uu____4873 =
                      let uu____4874 =
                        let uu____4875 = p_term false false e2  in
                        soft_parens_with_nesting uu____4875  in
                      let uu____4876 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4874 uu____4876  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4873  in
                  FStar_Pprint.op_Hat_Hat uu____4871 uu____4872  in
                FStar_Pprint.group uu____4870  in
              let uu____4877 =
                let uu____4878 = p_noSeqTerm ps pb e3  in jump2 uu____4878
                 in
              FStar_Pprint.op_Hat_Hat uu____4869 uu____4877  in
            FStar_Pprint.group uu____4868
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4879;_},e1::e2::e3::[])
            ->
            let uu____4885 =
              let uu____4886 =
                let uu____4887 =
                  let uu____4888 = p_atomicTermNotQUident e1  in
                  let uu____4889 =
                    let uu____4890 =
                      let uu____4891 =
                        let uu____4892 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4892  in
                      let uu____4893 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4891 uu____4893  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4890  in
                  FStar_Pprint.op_Hat_Hat uu____4888 uu____4889  in
                FStar_Pprint.group uu____4887  in
              let uu____4894 =
                let uu____4895 = p_noSeqTerm ps pb e3  in jump2 uu____4895
                 in
              FStar_Pprint.op_Hat_Hat uu____4886 uu____4894  in
            FStar_Pprint.group uu____4885
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4903 =
              let uu____4904 = str "requires"  in
              let uu____4905 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4904 uu____4905  in
            FStar_Pprint.group uu____4903
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4913 =
              let uu____4914 = str "ensures"  in
              let uu____4915 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4914 uu____4915  in
            FStar_Pprint.group uu____4913
        | FStar_Parser_AST.Attributes es ->
            let uu____4919 =
              let uu____4920 = str "attributes"  in
              let uu____4921 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4920 uu____4921  in
            FStar_Pprint.group uu____4919
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4925 =
                let uu____4926 =
                  let uu____4927 = str "if"  in
                  let uu____4928 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4927 uu____4928  in
                let uu____4929 =
                  let uu____4930 = str "then"  in
                  let uu____4931 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4930 uu____4931  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4926 uu____4929  in
              FStar_Pprint.group uu____4925
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4934,uu____4935,e31) when
                     is_unit e31 ->
                     let uu____4937 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4937
                 | uu____4938 -> p_noSeqTerm false false e2  in
               let uu____4939 =
                 let uu____4940 =
                   let uu____4941 = str "if"  in
                   let uu____4942 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4941 uu____4942  in
                 let uu____4943 =
                   let uu____4944 =
                     let uu____4945 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4945 e2_doc  in
                   let uu____4946 =
                     let uu____4947 = str "else"  in
                     let uu____4948 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4947 uu____4948  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4944 uu____4946  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4940 uu____4943  in
               FStar_Pprint.group uu____4939)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4971 =
              let uu____4972 =
                let uu____4973 =
                  let uu____4974 = str "try"  in
                  let uu____4975 = p_noSeqTerm false false e1  in
                  prefix2 uu____4974 uu____4975  in
                let uu____4976 =
                  let uu____4977 = str "with"  in
                  let uu____4978 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4977 uu____4978  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4973 uu____4976  in
              FStar_Pprint.group uu____4972  in
            let uu____4987 = paren_if (ps || pb)  in uu____4987 uu____4971
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5014 =
              let uu____5015 =
                let uu____5016 =
                  let uu____5017 = str "match"  in
                  let uu____5018 = p_noSeqTerm false false e1  in
                  let uu____5019 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5017 uu____5018 uu____5019
                   in
                let uu____5020 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5016 uu____5020  in
              FStar_Pprint.group uu____5015  in
            let uu____5029 = paren_if (ps || pb)  in uu____5029 uu____5014
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5036 =
              let uu____5037 =
                let uu____5038 =
                  let uu____5039 = str "let open"  in
                  let uu____5040 = p_quident uid  in
                  let uu____5041 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5039 uu____5040 uu____5041
                   in
                let uu____5042 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5038 uu____5042  in
              FStar_Pprint.group uu____5037  in
            let uu____5043 = paren_if ps  in uu____5043 uu____5036
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5107 is_last =
              match uu____5107 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5140 =
                          let uu____5141 = str "let"  in
                          let uu____5142 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5141 uu____5142
                           in
                        FStar_Pprint.group uu____5140
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5143 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5148 =
                    if is_last
                    then
                      let uu____5149 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5150 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5149 doc_expr uu____5150
                    else
                      (let uu____5152 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5152)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5148
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5198 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5198
                     else
                       (let uu____5206 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5206)) lbs
               in
            let lbs_doc =
              let uu____5214 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5214  in
            let uu____5215 =
              let uu____5216 =
                let uu____5217 =
                  let uu____5218 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5218
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5217  in
              FStar_Pprint.group uu____5216  in
            let uu____5219 = paren_if ps  in uu____5219 uu____5215
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5226;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5229;
                                                             FStar_Parser_AST.level
                                                               = uu____5230;_})
            when matches_var maybe_x x ->
            let uu____5257 =
              let uu____5258 =
                let uu____5259 = str "function"  in
                let uu____5260 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5259 uu____5260  in
              FStar_Pprint.group uu____5258  in
            let uu____5269 = paren_if (ps || pb)  in uu____5269 uu____5257
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5275 =
              let uu____5276 = str "quote"  in
              let uu____5277 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5276 uu____5277  in
            FStar_Pprint.group uu____5275
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5279 =
              let uu____5280 = str "`"  in
              let uu____5281 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5280 uu____5281  in
            FStar_Pprint.group uu____5279
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5283 =
              let uu____5284 = str "`%"  in
              let uu____5285 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5284 uu____5285  in
            FStar_Pprint.group uu____5283
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5287;
              FStar_Parser_AST.level = uu____5288;_}
            ->
            let uu____5289 =
              let uu____5290 = str "`@"  in
              let uu____5291 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5290 uu____5291  in
            FStar_Pprint.group uu____5289
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5293 =
              let uu____5294 = str "`#"  in
              let uu____5295 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5294 uu____5295  in
            FStar_Pprint.group uu____5293
        | uu____5296 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___114_5297  ->
    match uu___114_5297 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5309 =
          let uu____5310 = str "[@"  in
          let uu____5311 =
            let uu____5312 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5313 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5312 uu____5313  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5310 uu____5311  in
        FStar_Pprint.group uu____5309

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5339 =
                   let uu____5340 =
                     let uu____5341 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5341 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5340 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5339 term_doc
             | pats ->
                 let uu____5347 =
                   let uu____5348 =
                     let uu____5349 =
                       let uu____5350 =
                         let uu____5351 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5351
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5350 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5352 = p_trigger trigger  in
                     prefix2 uu____5349 uu____5352  in
                   FStar_Pprint.group uu____5348  in
                 prefix2 uu____5347 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5372 =
                   let uu____5373 =
                     let uu____5374 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5374 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5373 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5372 term_doc
             | pats ->
                 let uu____5380 =
                   let uu____5381 =
                     let uu____5382 =
                       let uu____5383 =
                         let uu____5384 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5384
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5383 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5385 = p_trigger trigger  in
                     prefix2 uu____5382 uu____5385  in
                   FStar_Pprint.group uu____5381  in
                 prefix2 uu____5380 term_doc)
        | uu____5386 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5388 -> str "forall"
    | FStar_Parser_AST.QExists uu____5401 -> str "exists"
    | uu____5414 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___115_5415  ->
    match uu___115_5415 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5427 =
          let uu____5428 =
            let uu____5429 =
              let uu____5430 = str "pattern"  in
              let uu____5431 =
                let uu____5432 =
                  let uu____5433 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5433
                   in
                FStar_Pprint.op_Hat_Hat uu____5432 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5430 uu____5431  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5429  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5428  in
        FStar_Pprint.group uu____5427

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5439 = str "\\/"  in
    FStar_Pprint.separate_map uu____5439 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5445 =
      let uu____5446 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5446 p_appTerm pats  in
    FStar_Pprint.group uu____5445

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5456 =
              let uu____5457 =
                let uu____5458 = str "fun"  in
                let uu____5459 =
                  let uu____5460 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5460
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5458 uu____5459  in
              let uu____5461 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5457 uu____5461  in
            let uu____5462 = paren_if ps  in uu____5462 uu____5456
        | uu____5467 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5471  ->
      match uu____5471 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5494 =
                    let uu____5495 =
                      let uu____5496 =
                        let uu____5497 = p_tuplePattern p  in
                        let uu____5498 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5497 uu____5498  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5496
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5495  in
                  FStar_Pprint.group uu____5494
              | FStar_Pervasives_Native.Some f ->
                  let uu____5500 =
                    let uu____5501 =
                      let uu____5502 =
                        let uu____5503 =
                          let uu____5504 =
                            let uu____5505 = p_tuplePattern p  in
                            let uu____5506 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5505
                              uu____5506
                             in
                          FStar_Pprint.group uu____5504  in
                        let uu____5507 =
                          let uu____5508 =
                            let uu____5511 = p_tmFormula f  in
                            [uu____5511; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5508  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5503 uu____5507
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5502
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5501  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5500
               in
            let uu____5512 =
              let uu____5513 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5513  in
            FStar_Pprint.group uu____5512  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5522 =
                      let uu____5523 =
                        let uu____5524 =
                          let uu____5525 =
                            let uu____5526 =
                              let uu____5527 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5527  in
                            FStar_Pprint.separate_map uu____5526
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5525
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5524
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5523  in
                    FStar_Pprint.group uu____5522
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5528 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5530;_},e1::e2::[])
        ->
        let uu____5535 = str "<==>"  in
        let uu____5536 = p_tmImplies e1  in
        let uu____5537 = p_tmIff e2  in
        infix0 uu____5535 uu____5536 uu____5537
    | uu____5538 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5540;_},e1::e2::[])
        ->
        let uu____5545 = str "==>"  in
        let uu____5546 = p_tmArrow p_tmFormula e1  in
        let uu____5547 = p_tmImplies e2  in
        infix0 uu____5545 uu____5546 uu____5547
    | uu____5548 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5556 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5556 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5577 ->
               let uu____5578 =
                 let uu____5579 =
                   let uu____5580 =
                     let uu____5581 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5581
                      in
                   FStar_Pprint.separate uu____5580 terms  in
                 let uu____5582 =
                   let uu____5583 =
                     let uu____5584 =
                       let uu____5585 =
                         let uu____5586 =
                           let uu____5587 =
                             let uu____5588 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5588
                              in
                           FStar_Pprint.separate uu____5587 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5586 last_op  in
                       let uu____5589 =
                         let uu____5590 =
                           let uu____5591 =
                             let uu____5592 =
                               let uu____5593 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5593
                                in
                             FStar_Pprint.separate uu____5592 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5591 last_op  in
                         jump2 uu____5590  in
                       FStar_Pprint.ifflat uu____5585 uu____5589  in
                     FStar_Pprint.group uu____5584  in
                   let uu____5594 = FStar_List.hd last1  in
                   prefix2 uu____5583 uu____5594  in
                 FStar_Pprint.ifflat uu____5579 uu____5582  in
               FStar_Pprint.group uu____5578)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5607 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5612 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5607 uu____5612
      | uu____5615 -> let uu____5616 = p_Tm e  in [uu____5616]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5619 =
        let uu____5620 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5620 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5619  in
    let disj =
      let uu____5622 =
        let uu____5623 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5623 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5622  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5642;_},e1::e2::[])
        ->
        let uu____5647 = p_tmDisjunction e1  in
        let uu____5652 = let uu____5657 = p_tmConjunction e2  in [uu____5657]
           in
        FStar_List.append uu____5647 uu____5652
    | uu____5666 -> let uu____5667 = p_tmConjunction e  in [uu____5667]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5677;_},e1::e2::[])
        ->
        let uu____5682 = p_tmConjunction e1  in
        let uu____5685 = let uu____5688 = p_tmTuple e2  in [uu____5688]  in
        FStar_List.append uu____5682 uu____5685
    | uu____5689 -> let uu____5690 = p_tmTuple e  in [uu____5690]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5707 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5707
          (fun uu____5715  ->
             match uu____5715 with | (e1,uu____5721) -> p_tmEq e1) args
    | uu____5722 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5727 =
             let uu____5728 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5728  in
           FStar_Pprint.group uu____5727)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
         in
      p_tmEqWith' p_X n1 e

and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               (let uu____5745 = FStar_Ident.text_of_id op  in
                uu____5745 = "="))
              ||
              (let uu____5747 = FStar_Ident.text_of_id op  in
               uu____5747 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5749 = levels op1  in
            (match uu____5749 with
             | (left1,mine,right1) ->
                 let uu____5759 =
                   let uu____5760 = FStar_All.pipe_left str op1  in
                   let uu____5761 = p_tmEqWith' p_X left1 e1  in
                   let uu____5762 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5760 uu____5761 uu____5762  in
                 paren_if_gt curr mine uu____5759)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5763;_},e1::e2::[])
            ->
            let uu____5768 =
              let uu____5769 = p_tmEqWith p_X e1  in
              let uu____5770 =
                let uu____5771 =
                  let uu____5772 =
                    let uu____5773 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5773  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5772  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5771  in
              FStar_Pprint.op_Hat_Hat uu____5769 uu____5770  in
            FStar_Pprint.group uu____5768
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5774;_},e1::[])
            ->
            let uu____5778 = levels "-"  in
            (match uu____5778 with
             | (left1,mine,right1) ->
                 let uu____5788 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5788)
        | uu____5789 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' false p_X n1 e

and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple  ->
    fun p_X  ->
      fun curr  ->
        fun e  ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid,(e1,uu____5833)::(e2,uu____5835)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5855 = is_list e  in Prims.op_Negation uu____5855)
              ->
              let op = "::"  in
              let uu____5857 = levels op  in
              (match uu____5857 with
               | (left1,mine,right1) ->
                   let uu____5867 =
                     let uu____5868 = str op  in
                     let uu____5869 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5870 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5868 uu____5869 uu____5870  in
                   paren_if_gt curr mine uu____5867)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5878 = levels op  in
              (match uu____5878 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5894 = p_binder false b  in
                     let uu____5895 =
                       let uu____5896 =
                         let uu____5897 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5897 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5896
                        in
                     FStar_Pprint.op_Hat_Hat uu____5894 uu____5895  in
                   let uu____5898 =
                     let uu____5899 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5900 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5899 uu____5900  in
                   paren_if_gt curr mine uu____5898)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5901;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5926 = levels op  in
              (match uu____5926 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5936 = str op  in
                     let uu____5937 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5938 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5936 uu____5937 uu____5938
                   else
                     (let uu____5940 =
                        let uu____5941 = str op  in
                        let uu____5942 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5943 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5941 uu____5942 uu____5943  in
                      paren_if_gt curr mine uu____5940))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5950 = levels op1  in
              (match uu____5950 with
               | (left1,mine,right1) ->
                   let uu____5960 =
                     let uu____5961 = str op1  in
                     let uu____5962 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5963 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5961 uu____5962 uu____5963  in
                   paren_if_gt curr mine uu____5960)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5982 =
                let uu____5983 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5984 =
                  let uu____5985 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5985 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5983 uu____5984  in
              braces_with_nesting uu____5982
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5990;_},e1::[])
              ->
              let uu____5994 =
                let uu____5995 = str "~"  in
                let uu____5996 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5995 uu____5996  in
              FStar_Pprint.group uu____5994
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____5998;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6004 = levels op  in
                   (match uu____6004 with
                    | (left1,mine,right1) ->
                        let uu____6014 =
                          let uu____6015 = str op  in
                          let uu____6016 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6017 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6015 uu____6016 uu____6017  in
                        paren_if_gt curr mine uu____6014)
               | uu____6018 -> p_X e)
          | uu____6019 -> p_X e

and (p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_appTerm e

and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_tmRefinement e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmNoEqWith p_tmRefinement e

and (p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid,e1) ->
        let uu____6026 =
          let uu____6027 = p_lident lid  in
          let uu____6028 =
            let uu____6029 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6029  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6027 uu____6028  in
        FStar_Pprint.group uu____6026
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6032 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6034 = p_appTerm e  in
    let uu____6035 =
      let uu____6036 =
        let uu____6037 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6037 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6036  in
    FStar_Pprint.op_Hat_Hat uu____6034 uu____6035

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6042 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6042 t phi
      | FStar_Parser_AST.TAnnotated uu____6043 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6048 ->
          let uu____6049 =
            let uu____6050 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6050
             in
          failwith uu____6049
      | FStar_Parser_AST.TVariable uu____6051 ->
          let uu____6052 =
            let uu____6053 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6053
             in
          failwith uu____6052
      | FStar_Parser_AST.NoName uu____6054 ->
          let uu____6055 =
            let uu____6056 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6056
             in
          failwith uu____6055

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6058  ->
      match uu____6058 with
      | (lid,e) ->
          let uu____6065 =
            let uu____6066 = p_qlident lid  in
            let uu____6067 =
              let uu____6068 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6068
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6066 uu____6067  in
          FStar_Pprint.group uu____6065

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6070 when is_general_application e ->
        let uu____6077 = head_and_args e  in
        (match uu____6077 with
         | (head1,args) ->
             let uu____6102 =
               let uu____6113 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6113
               then
                 let uu____6143 =
                   FStar_Util.take
                     (fun uu____6167  ->
                        match uu____6167 with
                        | (uu____6172,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6143 with
                 | (fs_typ_args,args1) ->
                     let uu____6210 =
                       let uu____6211 = p_indexingTerm head1  in
                       let uu____6212 =
                         let uu____6213 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6213 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6211 uu____6212  in
                     (uu____6210, args1)
               else
                 (let uu____6225 = p_indexingTerm head1  in
                  (uu____6225, args))
                in
             (match uu____6102 with
              | (head_doc,args1) ->
                  let uu____6246 =
                    let uu____6247 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6247 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6246))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6267 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6267)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6285 =
               let uu____6286 = p_quident lid  in
               let uu____6287 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6286 uu____6287  in
             FStar_Pprint.group uu____6285
         | hd1::tl1 ->
             let uu____6304 =
               let uu____6305 =
                 let uu____6306 =
                   let uu____6307 = p_quident lid  in
                   let uu____6308 = p_argTerm hd1  in
                   prefix2 uu____6307 uu____6308  in
                 FStar_Pprint.group uu____6306  in
               let uu____6309 =
                 let uu____6310 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6310  in
               FStar_Pprint.op_Hat_Hat uu____6305 uu____6309  in
             FStar_Pprint.group uu____6304)
    | uu____6315 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____6324 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6324 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6326 = str "#"  in
        let uu____6327 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6326 uu____6327
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6330 = str "#["  in
        let uu____6331 =
          let uu____6332 = p_indexingTerm t  in
          let uu____6333 =
            let uu____6334 = str "]"  in
            let uu____6335 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6334 uu____6335  in
          FStar_Pprint.op_Hat_Hat uu____6332 uu____6333  in
        FStar_Pprint.op_Hat_Hat uu____6330 uu____6331
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6337  ->
    match uu____6337 with | (e,uu____6343) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6348;_},e1::e2::[])
          ->
          let uu____6353 =
            let uu____6354 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6355 =
              let uu____6356 =
                let uu____6357 = p_term false false e2  in
                soft_parens_with_nesting uu____6357  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6356  in
            FStar_Pprint.op_Hat_Hat uu____6354 uu____6355  in
          FStar_Pprint.group uu____6353
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6358;_},e1::e2::[])
          ->
          let uu____6363 =
            let uu____6364 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6365 =
              let uu____6366 =
                let uu____6367 = p_term false false e2  in
                soft_brackets_with_nesting uu____6367  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6366  in
            FStar_Pprint.op_Hat_Hat uu____6364 uu____6365  in
          FStar_Pprint.group uu____6363
      | uu____6368 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6373 = p_quident lid  in
        let uu____6374 =
          let uu____6375 =
            let uu____6376 = p_term false false e1  in
            soft_parens_with_nesting uu____6376  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6375  in
        FStar_Pprint.op_Hat_Hat uu____6373 uu____6374
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6382 =
          let uu____6383 = FStar_Ident.text_of_id op  in str uu____6383  in
        let uu____6384 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6382 uu____6384
    | uu____6385 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____6394 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6401 =
          let uu____6402 = FStar_Ident.text_of_id op  in str uu____6402  in
        let uu____6403 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6401 uu____6403
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6407 =
          let uu____6408 =
            let uu____6409 =
              let uu____6410 = FStar_Ident.text_of_id op  in str uu____6410
               in
            let uu____6411 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6409 uu____6411  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6408  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6407
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6426 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6427 =
          let uu____6428 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6429 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6428 p_tmEq uu____6429  in
        let uu____6436 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6426 uu____6427 uu____6436
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6439 =
          let uu____6440 = p_atomicTermNotQUident e1  in
          let uu____6441 =
            let uu____6442 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6442  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6440 uu____6441
           in
        FStar_Pprint.group uu____6439
    | uu____6443 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6448 = p_quident constr_lid  in
        let uu____6449 =
          let uu____6450 =
            let uu____6451 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6451  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6450  in
        FStar_Pprint.op_Hat_Hat uu____6448 uu____6449
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6453 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6453 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6455 = p_term false false e1  in
        soft_parens_with_nesting uu____6455
    | uu____6456 when is_array e ->
        let es = extract_from_list e  in
        let uu____6460 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6461 =
          let uu____6462 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6462
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6465 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6460 uu____6461 uu____6465
    | uu____6466 when is_list e ->
        let uu____6467 =
          let uu____6468 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6469 = extract_from_list e  in
          separate_map_or_flow_last uu____6468
            (fun ps  -> p_noSeqTerm ps false) uu____6469
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6467 FStar_Pprint.rbracket
    | uu____6474 when is_lex_list e ->
        let uu____6475 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6476 =
          let uu____6477 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6478 = extract_from_list e  in
          separate_map_or_flow_last uu____6477
            (fun ps  -> p_noSeqTerm ps false) uu____6478
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6475 uu____6476 FStar_Pprint.rbracket
    | uu____6483 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6487 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6488 =
          let uu____6489 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6489 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6487 uu____6488 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6493 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6494 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6493 uu____6494
    | FStar_Parser_AST.Op (op,args) when
        let uu____6501 = handleable_op op args  in
        Prims.op_Negation uu____6501 ->
        let uu____6502 =
          let uu____6503 =
            let uu____6504 = FStar_Ident.text_of_id op  in
            let uu____6505 =
              let uu____6506 =
                let uu____6507 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6507
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6506  in
            Prims.strcat uu____6504 uu____6505  in
          Prims.strcat "Operation " uu____6503  in
        failwith uu____6502
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6509 = str "u#"  in
        let uu____6510 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6509 uu____6510
    | FStar_Parser_AST.Wild  ->
        let uu____6511 = p_term false false e  in
        soft_parens_with_nesting uu____6511
    | FStar_Parser_AST.Const uu____6512 ->
        let uu____6513 = p_term false false e  in
        soft_parens_with_nesting uu____6513
    | FStar_Parser_AST.Op uu____6514 ->
        let uu____6521 = p_term false false e  in
        soft_parens_with_nesting uu____6521
    | FStar_Parser_AST.Tvar uu____6522 ->
        let uu____6523 = p_term false false e  in
        soft_parens_with_nesting uu____6523
    | FStar_Parser_AST.Var uu____6524 ->
        let uu____6525 = p_term false false e  in
        soft_parens_with_nesting uu____6525
    | FStar_Parser_AST.Name uu____6526 ->
        let uu____6527 = p_term false false e  in
        soft_parens_with_nesting uu____6527
    | FStar_Parser_AST.Construct uu____6528 ->
        let uu____6539 = p_term false false e  in
        soft_parens_with_nesting uu____6539
    | FStar_Parser_AST.Abs uu____6540 ->
        let uu____6547 = p_term false false e  in
        soft_parens_with_nesting uu____6547
    | FStar_Parser_AST.App uu____6548 ->
        let uu____6555 = p_term false false e  in
        soft_parens_with_nesting uu____6555
    | FStar_Parser_AST.Let uu____6556 ->
        let uu____6577 = p_term false false e  in
        soft_parens_with_nesting uu____6577
    | FStar_Parser_AST.LetOpen uu____6578 ->
        let uu____6583 = p_term false false e  in
        soft_parens_with_nesting uu____6583
    | FStar_Parser_AST.Seq uu____6584 ->
        let uu____6589 = p_term false false e  in
        soft_parens_with_nesting uu____6589
    | FStar_Parser_AST.Bind uu____6590 ->
        let uu____6597 = p_term false false e  in
        soft_parens_with_nesting uu____6597
    | FStar_Parser_AST.If uu____6598 ->
        let uu____6605 = p_term false false e  in
        soft_parens_with_nesting uu____6605
    | FStar_Parser_AST.Match uu____6606 ->
        let uu____6621 = p_term false false e  in
        soft_parens_with_nesting uu____6621
    | FStar_Parser_AST.TryWith uu____6622 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Ascribed uu____6638 ->
        let uu____6647 = p_term false false e  in
        soft_parens_with_nesting uu____6647
    | FStar_Parser_AST.Record uu____6648 ->
        let uu____6661 = p_term false false e  in
        soft_parens_with_nesting uu____6661
    | FStar_Parser_AST.Project uu____6662 ->
        let uu____6667 = p_term false false e  in
        soft_parens_with_nesting uu____6667
    | FStar_Parser_AST.Product uu____6668 ->
        let uu____6675 = p_term false false e  in
        soft_parens_with_nesting uu____6675
    | FStar_Parser_AST.Sum uu____6676 ->
        let uu____6683 = p_term false false e  in
        soft_parens_with_nesting uu____6683
    | FStar_Parser_AST.QForall uu____6684 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.QExists uu____6698 ->
        let uu____6711 = p_term false false e  in
        soft_parens_with_nesting uu____6711
    | FStar_Parser_AST.Refine uu____6712 ->
        let uu____6717 = p_term false false e  in
        soft_parens_with_nesting uu____6717
    | FStar_Parser_AST.NamedTyp uu____6718 ->
        let uu____6723 = p_term false false e  in
        soft_parens_with_nesting uu____6723
    | FStar_Parser_AST.Requires uu____6724 ->
        let uu____6731 = p_term false false e  in
        soft_parens_with_nesting uu____6731
    | FStar_Parser_AST.Ensures uu____6732 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.Attributes uu____6740 ->
        let uu____6743 = p_term false false e  in
        soft_parens_with_nesting uu____6743
    | FStar_Parser_AST.Quote uu____6744 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.VQuote uu____6750 ->
        let uu____6751 = p_term false false e  in
        soft_parens_with_nesting uu____6751
    | FStar_Parser_AST.Antiquote uu____6752 ->
        let uu____6753 = p_term false false e  in
        soft_parens_with_nesting uu____6753

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___118_6754  ->
    match uu___118_6754 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6760) ->
        let uu____6761 = str s  in FStar_Pprint.dquotes uu____6761
    | FStar_Const.Const_bytearray (bytes,uu____6763) ->
        let uu____6770 =
          let uu____6771 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6771  in
        let uu____6772 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6770 uu____6772
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___116_6792 =
          match uu___116_6792 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___117_6798 =
          match uu___117_6798 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6809  ->
               match uu____6809 with
               | (s,w) ->
                   let uu____6816 = signedness s  in
                   let uu____6817 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6816 uu____6817)
            sign_width_opt
           in
        let uu____6818 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6818 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6820 = FStar_Range.string_of_range r  in str uu____6820
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6822 = p_quident lid  in
        let uu____6823 =
          let uu____6824 =
            let uu____6825 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6825  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6824  in
        FStar_Pprint.op_Hat_Hat uu____6822 uu____6823

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6827 = str "u#"  in
    let uu____6828 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6827 uu____6828

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6830;_},u1::u2::[])
        ->
        let uu____6835 =
          let uu____6836 = p_universeFrom u1  in
          let uu____6837 =
            let uu____6838 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6838  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6836 uu____6837  in
        FStar_Pprint.group uu____6835
    | FStar_Parser_AST.App uu____6839 ->
        let uu____6846 = head_and_args u  in
        (match uu____6846 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6872 =
                    let uu____6873 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6874 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6882  ->
                           match uu____6882 with
                           | (u1,uu____6888) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6873 uu____6874  in
                  FStar_Pprint.group uu____6872
              | uu____6889 ->
                  let uu____6890 =
                    let uu____6891 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6891
                     in
                  failwith uu____6890))
    | uu____6892 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6915 = FStar_Ident.text_of_id id1  in str uu____6915
    | FStar_Parser_AST.Paren u1 ->
        let uu____6917 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6917
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6918;_},uu____6919::uu____6920::[])
        ->
        let uu____6923 = p_universeFrom u  in
        soft_parens_with_nesting uu____6923
    | FStar_Parser_AST.App uu____6924 ->
        let uu____6931 = p_universeFrom u  in
        soft_parens_with_nesting uu____6931
    | uu____6932 ->
        let uu____6933 =
          let uu____6934 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6934
           in
        failwith uu____6933

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
  
let (signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document)
  = fun e  -> p_justSig e 
let (decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun e  -> p_decl e 
let (pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  -> p_disjunctivePattern p 
let (binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun b  -> p_binder true b 
let (modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document) =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____7006,decls) ->
           let uu____7012 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7012
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7021,decls,uu____7023) ->
           let uu____7028 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7028
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7081  ->
         match uu____7081 with | (comment,range) -> str comment) comments
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____7125,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7131,decls,uu____7133) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7178 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7191;
                 FStar_Parser_AST.doc = uu____7192;
                 FStar_Parser_AST.quals = uu____7193;
                 FStar_Parser_AST.attrs = uu____7194;_}::uu____7195 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7201 =
                   let uu____7204 =
                     let uu____7207 = FStar_List.tl ds  in d :: uu____7207
                      in
                   d0 :: uu____7204  in
                 (uu____7201, (d0.FStar_Parser_AST.drange))
             | uu____7212 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7178 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7272 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7272 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7368 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7368, comments1))))))
  