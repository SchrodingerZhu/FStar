open Prims
let (one_toplevel :
  FStar_Parser_AST.decl Prims.list ->
    (FStar_Parser_AST.decl,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun decls  ->
    let uu____18 =
      FStar_List.partition
        (fun d  ->
           match d.FStar_Parser_AST.d with
           | FStar_Parser_AST.TopLevelModule uu____30 -> true
           | uu____31 -> false) decls
       in
    match uu____18 with
    | (top,nontops) ->
        (match top with
         | t::[] -> FStar_Pervasives_Native.Some (t, nontops)
         | uu____67 -> FStar_Pervasives_Native.None)
  
type mforest =
  | Leaf of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 
  | Branch of mforest FStar_Util.smap 
let (uu___is_Leaf : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Leaf _0 -> true | uu____102 -> false
  
let (__proj__Leaf__item___0 :
  mforest -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Leaf _0 -> _0 
let (uu___is_Branch : mforest -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branch _0 -> true | uu____130 -> false
  
let (__proj__Branch__item___0 : mforest -> mforest FStar_Util.smap) =
  fun projectee  -> match projectee with | Branch _0 -> _0 
let (htree : mforest FStar_Util.smap) =
  FStar_Util.smap_create (Prims.parse_int "50") 
let string_of_optiont :
  'Auu____156 'Auu____157 .
    ('Auu____156 -> 'Auu____157) ->
      'Auu____157 ->
        'Auu____156 FStar_Pervasives_Native.option -> 'Auu____157
  =
  fun f  ->
    fun y  ->
      fun xo  ->
        match xo with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> y
  
let (string_of_fsdoco :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
    Prims.string)
  =
  fun d  ->
    string_of_optiont
      (fun x  ->
         let uu____235 =
           let uu____236 = FStar_Parser_AST.string_of_fsdoc x  in
           Prims.strcat uu____236 "*)"  in
         Prims.strcat "(*" uu____235) "" d
  
let (string_of_termo :
  FStar_Parser_AST.term FStar_Pervasives_Native.option -> Prims.string) =
  fun t  -> string_of_optiont FStar_Parser_AST.term_to_string "" t 
let (code_wrap : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "```fsharp\n" (Prims.strcat s "\n```\n") 
let (string_of_tycon : FStar_Parser_AST.tycon -> Prims.string) =
  fun tycon  ->
    match tycon with
    | FStar_Parser_AST.TyconAbstract uu____256 -> "abstract"
    | FStar_Parser_AST.TyconAbbrev uu____267 -> "abbrev"
    | FStar_Parser_AST.TyconRecord (id1,_bb,_ko,fields) ->
        let uu____312 =
          let uu____313 =
            let uu____314 =
              let uu____315 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____364  ->
                        match uu____364 with
                        | (id2,t,doco) ->
                            let uu____410 = string_of_fsdoco doco  in
                            let uu____411 =
                              let uu____412 =
                                let uu____413 =
                                  FStar_Parser_AST.term_to_string t  in
                                Prims.strcat ":" uu____413  in
                              Prims.strcat id2.FStar_Ident.idText uu____412
                               in
                            Prims.strcat uu____410 uu____411))
                 in
              FStar_All.pipe_right uu____315 (FStar_String.concat "; ")  in
            Prims.strcat uu____314 " }"  in
          Prims.strcat " = { " uu____313  in
        Prims.strcat id1.FStar_Ident.idText uu____312
    | FStar_Parser_AST.TyconVariant (id1,_bb,_ko,vars) ->
        let uu____456 =
          let uu____457 =
            let uu____458 =
              FStar_All.pipe_right vars
                (FStar_List.map
                   (fun uu____516  ->
                      match uu____516 with
                      | (id2,trmo,doco,u) ->
                          let uu____571 = string_of_fsdoco doco  in
                          let uu____572 =
                            let uu____573 =
                              let uu____574 =
                                string_of_optiont
                                  FStar_Parser_AST.term_to_string "" trmo
                                 in
                              Prims.strcat ":" uu____574  in
                            Prims.strcat id2.FStar_Ident.idText uu____573  in
                          Prims.strcat uu____571 uu____572))
               in
            FStar_All.pipe_right uu____458 (FStar_String.concat " | ")  in
          Prims.strcat " = " uu____457  in
        Prims.strcat id1.FStar_Ident.idText uu____456
  
let (string_of_decl' : FStar_Parser_AST.decl' -> Prims.string) =
  fun d  ->
    match d with
    | FStar_Parser_AST.TopLevelModule l ->
        Prims.strcat "module " l.FStar_Ident.str
    | FStar_Parser_AST.Open l -> Prims.strcat "open " l.FStar_Ident.str
    | FStar_Parser_AST.Include l -> Prims.strcat "include " l.FStar_Ident.str
    | FStar_Parser_AST.ModuleAbbrev (i,l) ->
        Prims.strcat "module "
          (Prims.strcat i.FStar_Ident.idText
             (Prims.strcat " = " l.FStar_Ident.str))
    | FStar_Parser_AST.TopLevelLet (uu____587,pats) ->
        let termty =
          FStar_List.map
            (fun uu____621  ->
               match uu____621 with
               | (p,t) ->
                   let uu____632 = FStar_Parser_AST.pat_to_string p  in
                   let uu____633 = FStar_Parser_AST.term_to_string t  in
                   (uu____632, uu____633)) pats
           in
        let termty' =
          FStar_List.map
            (fun uu____644  ->
               match uu____644 with
               | (p,t) -> Prims.strcat p (Prims.strcat ":" t)) termty
           in
        Prims.strcat "let " (FStar_String.concat ", " termty')
    | FStar_Parser_AST.Main uu____651 -> "main ..."
    | FStar_Parser_AST.Assume (i,t) ->
        let uu____654 =
          let uu____655 =
            let uu____656 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____656  in
          Prims.strcat i.FStar_Ident.idText uu____655  in
        Prims.strcat "assume " uu____654
    | FStar_Parser_AST.Tycon (uu____657,tc,tys) ->
        let s = if tc then "class" else "type"  in
        let uu____678 =
          let uu____679 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____723  ->
                    match uu____723 with
                    | (t,d1) ->
                        let uu____766 = string_of_tycon t  in
                        let uu____767 =
                          let uu____768 = string_of_fsdoco d1  in
                          Prims.strcat " " uu____768  in
                        Prims.strcat uu____766 uu____767))
             in
          FStar_All.pipe_right uu____679 (FStar_String.concat " and ")  in
        Prims.strcat s uu____678
    | FStar_Parser_AST.Val (i,t) ->
        let uu____773 =
          let uu____774 =
            let uu____775 = FStar_Parser_AST.term_to_string t  in
            Prims.strcat ":" uu____775  in
          Prims.strcat i.FStar_Ident.idText uu____774  in
        Prims.strcat "val " uu____773
    | FStar_Parser_AST.Exception (i,uu____777) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
        (i,uu____783,uu____784,uu____785)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
        (i,uu____795,uu____796)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | FStar_Parser_AST.SubEffect uu____801 -> "sub_effect"
    | FStar_Parser_AST.Pragma uu____802 -> "pragma"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____809 = FStar_Parser_AST.term_to_string t  in
        Prims.strcat "splice " uu____809
    | FStar_Parser_AST.Fsdoc (comm,uu____811) -> comm
  
let (decl_documented : FStar_Parser_AST.decl -> Prims.bool) =
  fun d  ->
    let tycon_documented tt =
      let tyconvars_documented tycon =
        match tycon with
        | FStar_Parser_AST.TyconAbstract uu____857 -> false
        | FStar_Parser_AST.TyconAbbrev uu____868 -> false
        | FStar_Parser_AST.TyconRecord (uu____881,uu____882,uu____883,fields)
            ->
            FStar_List.existsb
              (fun uu____925  ->
                 match uu____925 with
                 | (_id,_t,doco) -> FStar_Util.is_some doco) fields
        | FStar_Parser_AST.TyconVariant (uu____941,uu____942,uu____943,vars)
            ->
            FStar_List.existsb
              (fun uu____998  ->
                 match uu____998 with
                 | (_id,_t,doco,_u) -> FStar_Util.is_some doco) vars
         in
      FStar_List.existsb
        (fun uu____1032  ->
           match uu____1032 with
           | (tycon,doco) ->
               (tyconvars_documented tycon) || (FStar_Util.is_some doco)) tt
       in
    match d.FStar_Parser_AST.doc with
    | FStar_Pervasives_Native.Some uu____1045 -> true
    | uu____1046 ->
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____1049 -> true
         | FStar_Parser_AST.Tycon (uu____1050,uu____1051,ty) ->
             tycon_documented ty
         | uu____1069 -> false)
  
let (document_decl : (Prims.string -> unit) -> FStar_Parser_AST.decl -> unit)
  =
  fun w  ->
    fun d  ->
      if decl_documented d
      then
        let uu____1085 = d  in
        match uu____1085 with
        | { FStar_Parser_AST.d = decl; FStar_Parser_AST.drange = uu____1087;
            FStar_Parser_AST.doc = fsdoc;
            FStar_Parser_AST.quals = uu____1089;
            FStar_Parser_AST.attrs = uu____1090;_} ->
            ((let uu____1094 =
                let uu____1095 = string_of_decl' d.FStar_Parser_AST.d  in
                code_wrap uu____1095  in
              w uu____1094);
             (match fsdoc with
              | FStar_Pervasives_Native.Some (doc1,_kw) ->
                  w (Prims.strcat "\n" doc1)
              | uu____1111 -> ());
             w "")
      else ()
  
let document_toplevel :
  'Auu____1121 .
    'Auu____1121 ->
      FStar_Parser_AST.decl ->
        (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun name  ->
    fun topdecl  ->
      match topdecl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1140 ->
          (match topdecl.FStar_Parser_AST.doc with
           | FStar_Pervasives_Native.Some (doc1,kw) ->
               let uu____1163 =
                 FStar_List.tryFind
                   (fun uu____1177  ->
                      match uu____1177 with | (k,v1) -> k = "summary") kw
                  in
               (match uu____1163 with
                | FStar_Pervasives_Native.None  ->
                    (FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some doc1))
                | FStar_Pervasives_Native.Some (uu____1200,summary) ->
                    ((FStar_Pervasives_Native.Some summary),
                      (FStar_Pervasives_Native.Some doc1)))
           | FStar_Pervasives_Native.None  ->
               (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
      | uu____1214 ->
          FStar_Errors.raise_err
            (FStar_Errors.Fatal_NotTopLevelModule, "Not Top-level Module")
  
let (document_module : FStar_Parser_AST.modul -> FStar_Ident.lident) =
  fun m  ->
    let uu____1228 =
      match m with
      | FStar_Parser_AST.Module (n1,d) -> (n1, d, "module")
      | FStar_Parser_AST.Interface (n1,d,uu____1255) -> (n1, d, "interface")
       in
    match uu____1228 with
    | (name,decls,_mt) ->
        let uu____1269 = one_toplevel decls  in
        (match uu____1269 with
         | FStar_Pervasives_Native.Some (top_decl,other_decls) ->
             let on =
               FStar_Options.prepend_output_dir
                 (Prims.strcat name.FStar_Ident.str ".md")
                in
             let fd = FStar_Util.open_file_for_writing on  in
             let w = FStar_Util.append_to_file fd  in
             let no_summary = "fsdoc: no-summary-found"  in
             let no_comment = "fsdoc: no-comment-found"  in
             let uu____1299 = document_toplevel name top_decl  in
             (match uu____1299 with
              | (summary,comment) ->
                  let summary1 =
                    match summary with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_summary  in
                  let comment1 =
                    match comment with
                    | FStar_Pervasives_Native.Some s -> s
                    | FStar_Pervasives_Native.None  -> no_comment  in
                  ((let uu____1323 =
                      FStar_Util.format "# module %s" [name.FStar_Ident.str]
                       in
                    w uu____1323);
                   (let uu____1325 = FStar_Util.format "%s\n" [summary1]  in
                    w uu____1325);
                   (let uu____1327 = FStar_Util.format "%s\n" [comment1]  in
                    w uu____1327);
                   FStar_List.iter (document_decl w) other_decls;
                   FStar_Util.close_file fd;
                   name))
         | FStar_Pervasives_Native.None  ->
             let uu____1336 =
               let uu____1341 =
                 FStar_Util.format1 "No singleton toplevel in module %s"
                   name.FStar_Ident.str
                  in
               (FStar_Errors.Fatal_NonSingletonTopLevel, uu____1341)  in
             FStar_Errors.raise_err uu____1336)
  
let (generate : Prims.string Prims.list -> unit) =
  fun files  ->
    let modules =
      FStar_List.map
        (fun fn  ->
           let uu____1357 = FStar_Parser_Driver.parse_file fn  in
           FStar_Pervasives_Native.fst uu____1357) files
       in
    let mods = FStar_List.map document_module modules  in
    let on = FStar_Options.prepend_output_dir "index.md"  in
    let fd = FStar_Util.open_file_for_writing on  in
    FStar_List.iter
      (fun m  ->
         let uu____1383 = FStar_Util.format "%s\n" [m.FStar_Ident.str]  in
         FStar_Util.append_to_file fd uu____1383) mods;
    FStar_Util.close_file fd
  