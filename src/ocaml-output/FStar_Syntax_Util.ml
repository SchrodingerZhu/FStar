open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____27 = FStar_ST.op_Bang tts_f  in
    match uu____27 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____72 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____72 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____76 =
      let uu____79 =
        let uu____82 =
          FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____82]  in
      FStar_List.append lid.FStar_Ident.ns uu____79  in
    FStar_Ident.lid_of_ids uu____76
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____89 .
    (FStar_Syntax_Syntax.bv,'Auu____89) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____89) FStar_Pervasives_Native.tuple2
  =
  fun uu____101  ->
    match uu____101 with
    | (b,imp) ->
        let uu____108 = FStar_Syntax_Syntax.bv_to_name b  in (uu____108, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____131 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____131
            then []
            else (let uu____143 = arg_of_non_null_binder b  in [uu____143])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____167 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____213 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____213
              then
                let b1 =
                  let uu____231 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____231, (FStar_Pervasives_Native.snd b))  in
                let uu____232 = arg_of_non_null_binder b1  in (b1, uu____232)
              else
                (let uu____246 = arg_of_non_null_binder b  in (b, uu____246))))
       in
    FStar_All.pipe_right uu____167 FStar_List.unzip
  
let (name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____328 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____328
              then
                let uu____333 = b  in
                match uu____333 with
                | (a,imp) ->
                    let b1 =
                      let uu____341 =
                        let uu____342 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____342  in
                      FStar_Ident.id_of_text uu____341  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____374 =
          let uu____377 =
            let uu____378 =
              let uu____391 = name_binders binders  in (uu____391, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____378  in
          FStar_Syntax_Syntax.mk uu____377  in
        uu____374 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____409 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____449  ->
            match uu____449 with
            | (t,imp) ->
                let uu____460 =
                  let uu____461 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____461
                   in
                (uu____460, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____511  ->
            match uu____511 with
            | (t,imp) ->
                let uu____528 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____528, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____538 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____538
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____547 . 'Auu____547 -> 'Auu____547 Prims.list =
  fun s  -> [s] 
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals  ->
    fun actuals  ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f  ->
             fun a  ->
               fun out  ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
  
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____634  ->
             fun uu____635  ->
               match (uu____634, uu____635) with
               | ((x,uu____653),(y,uu____655)) ->
                   let uu____664 =
                     let uu____671 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____671)  in
                   FStar_Syntax_Syntax.NT uu____664) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____678) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____684,uu____685) -> unmeta e2
    | uu____726 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____737 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____744 -> e1
         | uu____753 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____755,uu____756) ->
        unmeta_safe e2
    | uu____797 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____809 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____810 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____820 = univ_kernel u1  in
        (match uu____820 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____831 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____838 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____846 = univ_kernel u  in FStar_Pervasives_Native.snd uu____846
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____857,uu____858) ->
          failwith "Impossible: compare_univs"
      | (uu____859,FStar_Syntax_Syntax.U_bvar uu____860) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____861) ->
          ~- (Prims.parse_int "1")
      | (uu____862,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____863) -> ~- (Prims.parse_int "1")
      | (uu____864,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____867,FStar_Syntax_Syntax.U_unif
         uu____868) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____877,FStar_Syntax_Syntax.U_name
         uu____878) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____905 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____906 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____905 - uu____906
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____937 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____937
                 (fun uu____952  ->
                    match uu____952 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____966,uu____967) ->
          ~- (Prims.parse_int "1")
      | (uu____970,FStar_Syntax_Syntax.U_max uu____971) ->
          (Prims.parse_int "1")
      | uu____974 ->
          let uu____979 = univ_kernel u1  in
          (match uu____979 with
           | (k1,n1) ->
               let uu____986 = univ_kernel u2  in
               (match uu____986 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____1001 = compare_univs u1 u2  in
      uu____1001 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____1012 =
        let uu____1013 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1013;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____1012
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1028 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1037 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1057 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1066 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____1090 =
          let uu____1091 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1091  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1090;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____1118 =
          let uu____1119 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____1119  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1118;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let uu___52_1148 = c  in
      let uu____1149 =
        let uu____1150 =
          let uu___53_1151 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___53_1151.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___53_1151.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___53_1151.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___53_1151.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1150  in
      {
        FStar_Syntax_Syntax.n = uu____1149;
        FStar_Syntax_Syntax.pos = (uu___52_1148.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___52_1148.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1166 -> c
        | FStar_Syntax_Syntax.GTotal uu____1175 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___54_1186 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___54_1186.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___54_1186.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___54_1186.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___54_1186.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___55_1187 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___55_1187.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___55_1187.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1190  ->
           let uu____1191 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1191)
  
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____1224 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1233 -> true
    | FStar_Syntax_Syntax.GTotal uu____1242 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___40_1261  ->
               match uu___40_1261 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1262 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___41_1269  ->
               match uu___41_1269 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1270 -> false)))
  
let (is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Parser_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___42_1277  ->
               match uu___42_1277 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1278 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___43_1289  ->
            match uu___43_1289 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1290 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___44_1297  ->
            match uu___44_1297 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1298 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1316 -> true
    | FStar_Syntax_Syntax.GTotal uu____1325 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___45_1338  ->
                   match uu___45_1338 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1339 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___46_1359  ->
               match uu___46_1359 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1360 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1367 =
      let uu____1368 = FStar_Syntax_Subst.compress t  in
      uu____1368.FStar_Syntax_Syntax.n  in
    match uu____1367 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1371,c) -> is_pure_or_ghost_comp c
    | uu____1389 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1398 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1402 =
      let uu____1403 = FStar_Syntax_Subst.compress t  in
      uu____1403.FStar_Syntax_Syntax.n  in
    match uu____1402 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1406,c) -> is_lemma_comp c
    | uu____1424 -> false
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax,
                                                            FStar_Syntax_Syntax.aqual)
                                                            FStar_Pervasives_Native.tuple2
                                                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1489 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.term'
                                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1554 = head_and_args' head1  in
        (match uu____1554 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1611 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1631) ->
        FStar_Syntax_Subst.compress t2
    | uu____1636 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1640 =
      let uu____1641 = FStar_Syntax_Subst.compress t  in
      uu____1641.FStar_Syntax_Syntax.n  in
    match uu____1640 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1644,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1666)::uu____1667 ->
                  let pats' = unmeta pats  in
                  let uu____1711 = head_and_args pats'  in
                  (match uu____1711 with
                   | (head1,uu____1727) ->
                       let uu____1748 =
                         let uu____1749 = un_uinst head1  in
                         uu____1749.FStar_Syntax_Syntax.n  in
                       (match uu____1748 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1753 -> false))
              | uu____1754 -> false)
         | uu____1763 -> false)
    | uu____1764 -> false
  
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___47_1776  ->
                   match uu___47_1776 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1777 -> false)))
    | uu____1778 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1791) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1801) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1821 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1830 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___56_1842 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___56_1842.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___56_1842.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___56_1842.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___56_1842.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___48_1853  ->
            match uu___48_1853 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1854 -> false))
  
let (primops : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.op_Eq;
  FStar_Parser_Const.op_notEq;
  FStar_Parser_Const.op_LT;
  FStar_Parser_Const.op_LTE;
  FStar_Parser_Const.op_GT;
  FStar_Parser_Const.op_GTE;
  FStar_Parser_Const.op_Subtraction;
  FStar_Parser_Const.op_Minus;
  FStar_Parser_Const.op_Addition;
  FStar_Parser_Const.op_Multiply;
  FStar_Parser_Const.op_Division;
  FStar_Parser_Const.op_Modulus;
  FStar_Parser_Const.op_And;
  FStar_Parser_Const.op_Or;
  FStar_Parser_Const.op_Negation] 
let (is_primop_lid : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____1870 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1876,uu____1877) ->
        unascribe e2
    | uu____1918 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
       FStar_Util.either,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1966,uu____1967) ->
          ascribe t' k
      | uu____2008 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____2032 =
      let uu____2037 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____2037  in
    uu____2032 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2082 =
      let uu____2083 = FStar_Syntax_Subst.compress t  in
      uu____2083.FStar_Syntax_Syntax.n  in
    match uu____2082 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2087 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2087
    | uu____2088 -> t
  
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun typ  ->
      fun k  ->
        fun r  ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange  in
          let i =
            let uu____2118 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2118;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____2124 =
      let uu____2137 = unascribe t  in head_and_args' uu____2137  in
    match uu____2124 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2161 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2165 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2169 -> false
  
let (injectives : Prims.string Prims.list) =
  ["FStar.Int8.int_to_t";
  "FStar.Int16.int_to_t";
  "FStar.Int32.int_to_t";
  "FStar.Int64.int_to_t";
  "FStar.UInt8.uint_to_t";
  "FStar.UInt16.uint_to_t";
  "FStar.UInt32.uint_to_t";
  "FStar.UInt64.uint_to_t";
  "FStar.Int8.__int_to_t";
  "FStar.Int16.__int_to_t";
  "FStar.Int32.__int_to_t";
  "FStar.Int64.__int_to_t";
  "FStar.UInt8.__uint_to_t";
  "FStar.UInt16.__uint_to_t";
  "FStar.UInt32.__uint_to_t";
  "FStar.UInt64.__uint_to_t"] 
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___49_2227 = if uu___49_2227 then Equal else Unknown  in
      let equal_iff uu___50_2232 = if uu___50_2232 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2246 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2254) -> NotEqual
        | (uu____2255,NotEqual ) -> NotEqual
        | (Unknown ,uu____2256) -> Unknown
        | (uu____2257,Unknown ) -> Unknown  in
      let equal_data f1 args1 f2 args2 =
        let uu____2295 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2295
        then
          let uu____2299 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2357  ->
                    match uu____2357 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2385 = eq_tm a1 a2  in
                        eq_inj acc uu____2385) Equal) uu____2299
        else NotEqual  in
      let uu____2387 =
        let uu____2392 =
          let uu____2393 = unmeta t11  in uu____2393.FStar_Syntax_Syntax.n
           in
        let uu____2396 =
          let uu____2397 = unmeta t21  in uu____2397.FStar_Syntax_Syntax.n
           in
        (uu____2392, uu____2396)  in
      match uu____2387 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2402,uu____2403) ->
          let uu____2404 = unlazy t11  in eq_tm uu____2404 t21
      | (uu____2405,FStar_Syntax_Syntax.Tm_lazy uu____2406) ->
          let uu____2407 = unlazy t21  in eq_tm t11 uu____2407
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          if
            (f.FStar_Syntax_Syntax.fv_qual =
               (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
              &&
              (g.FStar_Syntax_Syntax.fv_qual =
                 (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
          then equal_data f [] g []
          else
            (let uu____2425 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2425)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2438 = eq_tm f g  in
          eq_and uu____2438
            (fun uu____2441  ->
               let uu____2442 = eq_univs_list us vs  in equal_if uu____2442)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2443),uu____2444) -> Unknown
      | (uu____2445,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2446)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2449 = FStar_Const.eq_const c d  in equal_iff uu____2449
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2451),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2453)) ->
          let uu____2502 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2502
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2547 =
            let uu____2552 =
              let uu____2553 = un_uinst h1  in
              uu____2553.FStar_Syntax_Syntax.n  in
            let uu____2556 =
              let uu____2557 = un_uinst h2  in
              uu____2557.FStar_Syntax_Syntax.n  in
            (uu____2552, uu____2556)  in
          (match uu____2547 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (FStar_Pervasives_Native.Some
                       FStar_Syntax_Syntax.Data_ctor))
               -> equal_data f1 args1 f2 args2
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____2569 =
                    let uu____2570 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2570  in
                  FStar_List.mem uu____2569 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2571 ->
               let uu____2576 = eq_tm h1 h2  in
               eq_and uu____2576 (fun uu____2578  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____2683 = FStar_List.zip bs1 bs2  in
            let uu____2746 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____2783  ->
                 fun a  ->
                   match uu____2783 with
                   | (b1,b2) ->
                       eq_and a (fun uu____2876  -> branch_matches b1 b2))
              uu____2683 uu____2746
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2880 = eq_univs u v1  in equal_if uu____2880
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) -> if q1 = q2 then eq_tm t12 t22 else Unknown
      | uu____2894 -> Unknown

and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 -> eq_result)
  =
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____2971,uu____2972) -> false  in
      let uu____2981 = b1  in
      match uu____2981 with
      | (p1,w1,t1) ->
          let uu____3015 = b2  in
          (match uu____3015 with
           | (p2,w2,t2) ->
               let uu____3049 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____3049
               then
                 let uu____3050 =
                   (let uu____3053 = eq_tm t1 t2  in uu____3053 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____3062 = eq_tm t11 t21  in
                             uu____3062 = Equal) w1 w2)
                    in
                 (if uu____3050 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____3096)::a11,(b,uu____3099)::b1) ->
          let uu____3153 = eq_tm a b  in
          (match uu____3153 with
           | Equal  -> eq_args a11 b1
           | uu____3154 -> Unknown)
      | uu____3155 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3167) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3173,uu____3174) ->
        unrefine t2
    | uu____3215 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3219 =
      let uu____3220 = unrefine t  in uu____3220.FStar_Syntax_Syntax.n  in
    match uu____3219 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3225) -> is_unit t1
    | uu____3230 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3234 =
      let uu____3235 = unrefine t  in uu____3235.FStar_Syntax_Syntax.n  in
    match uu____3234 with
    | FStar_Syntax_Syntax.Tm_type uu____3238 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____3241) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3263) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____3268,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____3286 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____3290 =
      let uu____3291 = FStar_Syntax_Subst.compress e  in
      uu____3291.FStar_Syntax_Syntax.n  in
    match uu____3290 with
    | FStar_Syntax_Syntax.Tm_abs uu____3294 -> true
    | uu____3311 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3315 =
      let uu____3316 = FStar_Syntax_Subst.compress t  in
      uu____3316.FStar_Syntax_Syntax.n  in
    match uu____3315 with
    | FStar_Syntax_Syntax.Tm_arrow uu____3319 -> true
    | uu____3332 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____3338) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3344,uu____3345) ->
        pre_typ t2
    | uu____3386 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____3404 =
        let uu____3405 = un_uinst typ1  in uu____3405.FStar_Syntax_Syntax.n
         in
      match uu____3404 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____3460 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____3484 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____3500,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____3507) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____3512,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3523,uu____3524,uu____3525,uu____3526,uu____3527) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3537,uu____3538,uu____3539,uu____3540) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3546,uu____3547,uu____3548,uu____3549,uu____3550) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3556,uu____3557) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3559,uu____3560) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3563 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3564 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3565 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3576 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___51_3593  ->
    match uu___51_3593 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3603 'Auu____3604 .
    ('Auu____3603 FStar_Syntax_Syntax.syntax,'Auu____3604)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3614  ->
    match uu____3614 with | (hd1,uu____3622) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3631 'Auu____3632 .
    ('Auu____3631 FStar_Syntax_Syntax.syntax,'Auu____3632)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
  
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____3717 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____3769 = FStar_Ident.range_of_lid l  in
          let uu____3770 =
            let uu____3773 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____3773  in
          uu____3770 FStar_Pervasives_Native.None uu____3769
      | uu____3777 ->
          let e =
            let uu____3789 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____3789 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let (unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident) =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____3800 =
        let uu____3805 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____3805, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____3800
    else x
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let j = unmangle_field_name i  in
      let jtext = j.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int ->
        (FStar_Ident.lident,FStar_Syntax_Syntax.bv)
          FStar_Pervasives_Native.tuple2)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____3840 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____3840
          then
            let uu____3841 =
              let uu____3846 =
                let uu____3847 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____3847  in
              let uu____3848 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____3846, uu____3848)  in
            FStar_Ident.mk_ident uu____3841
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___57_3851 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___57_3851.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___57_3851.FStar_Syntax_Syntax.sort)
          }  in
        let uu____3852 = mk_field_projector_name_from_ident lid nm  in
        (uu____3852, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3863) -> ses
    | uu____3872 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____3879 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit) =
  fun uv  ->
    fun t  ->
      let uu____3886 = FStar_Syntax_Unionfind.find uv  in
      match uu____3886 with
      | FStar_Pervasives_Native.Some uu____3889 ->
          let uu____3890 =
            let uu____3891 =
              let uu____3892 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3892  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3891  in
          failwith uu____3890
      | uu____3893 -> FStar_Syntax_Unionfind.change uv t
  
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1  ->
    fun q2  ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator
         l1,FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector
         (l1a,l1b),FStar_Syntax_Syntax.Projector (l2a,l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | uu____3964 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____3995 =
                let uu___58_3996 = rc  in
                let uu____3997 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___58_3996.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3997;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___58_3996.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____3995
           in
        match bs with
        | [] -> t
        | uu____4008 ->
            let body =
              let uu____4010 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____4010  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____4038 =
                   let uu____4041 =
                     let uu____4042 =
                       let uu____4059 =
                         let uu____4066 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____4066 bs'  in
                       let uu____4077 = close_lopt lopt'  in
                       (uu____4059, t1, uu____4077)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4042  in
                   FStar_Syntax_Syntax.mk uu____4041  in
                 uu____4038 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____4093 ->
                 let uu____4100 =
                   let uu____4103 =
                     let uu____4104 =
                       let uu____4121 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____4122 = close_lopt lopt  in
                       (uu____4121, body, uu____4122)  in
                     FStar_Syntax_Syntax.Tm_abs uu____4104  in
                   FStar_Syntax_Syntax.mk uu____4103  in
                 uu____4100 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____4160 ->
          let uu____4167 =
            let uu____4170 =
              let uu____4171 =
                let uu____4184 = FStar_Syntax_Subst.close_binders bs  in
                let uu____4185 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____4184, uu____4185)  in
              FStar_Syntax_Syntax.Tm_arrow uu____4171  in
            FStar_Syntax_Syntax.mk uu____4170  in
          uu____4167 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____4216 =
        let uu____4217 = FStar_Syntax_Subst.compress t  in
        uu____4217.FStar_Syntax_Syntax.n  in
      match uu____4216 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____4243) ->
               let uu____4252 =
                 let uu____4253 = FStar_Syntax_Subst.compress tres  in
                 uu____4253.FStar_Syntax_Syntax.n  in
               (match uu____4252 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____4288 -> t)
           | uu____4289 -> t)
      | uu____4290 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____4299 =
        let uu____4300 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____4300 t.FStar_Syntax_Syntax.pos  in
      let uu____4301 =
        let uu____4304 =
          let uu____4305 =
            let uu____4312 =
              let uu____4313 =
                let uu____4314 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____4314]  in
              FStar_Syntax_Subst.close uu____4313 t  in
            (b, uu____4312)  in
          FStar_Syntax_Syntax.Tm_refine uu____4305  in
        FStar_Syntax_Syntax.mk uu____4304  in
      uu____4301 FStar_Pervasives_Native.None uu____4299
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____4363 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____4363 with
         | (bs1,c1) ->
             let uu____4380 = is_tot_or_gtot_comp c1  in
             if uu____4380
             then
               let uu____4391 = arrow_formals_comp (comp_result c1)  in
               (match uu____4391 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____4437;
           FStar_Syntax_Syntax.index = uu____4438;
           FStar_Syntax_Syntax.sort = k2;_},uu____4440)
        -> arrow_formals_comp k2
    | uu____4447 ->
        let uu____4448 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4448)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____4474 = arrow_formals_comp k  in
    match uu____4474 with | (bs,c) -> (bs, (comp_result c))
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.residual_comp
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____4550 =
            let uu___59_4551 = rc  in
            let uu____4552 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___59_4551.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____4552;
              FStar_Syntax_Syntax.residual_flags =
                (uu___59_4551.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____4550
      | uu____4559 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4587 =
        let uu____4588 =
          let uu____4591 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4591  in
        uu____4588.FStar_Syntax_Syntax.n  in
      match uu____4587 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4629 = aux t2 what  in
          (match uu____4629 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4689 -> ([], t1, abs_body_lcomp)  in
    let uu____4702 = aux t FStar_Pervasives_Native.None  in
    match uu____4702 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4744 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____4744 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              fun pos  ->
                {
                  FStar_Syntax_Syntax.lbname = lbname;
                  FStar_Syntax_Syntax.lbunivs = univ_vars;
                  FStar_Syntax_Syntax.lbtyp = typ;
                  FStar_Syntax_Syntax.lbeff = eff;
                  FStar_Syntax_Syntax.lbdef = def;
                  FStar_Syntax_Syntax.lbattrs = lbattrs;
                  FStar_Syntax_Syntax.lbpos = pos
                }
  
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                fun pos  ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None ,uu____4875) -> def
                    | (uu____4886,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____4898) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _0_27  ->
                                  FStar_Syntax_Syntax.U_name _0_27))
                           in
                        let inst1 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst1 def
                     in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ
                     in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1  in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
  
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple3)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____4998 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____4998 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____5027 ->
            let t' = arrow binders c  in
            let uu____5037 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____5037 with
             | (uvs1,t'1) ->
                 let uu____5056 =
                   let uu____5057 = FStar_Syntax_Subst.compress t'1  in
                   uu____5057.FStar_Syntax_Syntax.n  in
                 (match uu____5056 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____5098 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____5115 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____5120 -> false
  
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid 
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid 
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid 
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v 
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5152 =
        let uu____5153 = pre_typ t  in uu____5153.FStar_Syntax_Syntax.n  in
      match uu____5152 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____5157 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____5164 =
        let uu____5165 = pre_typ t  in uu____5165.FStar_Syntax_Syntax.n  in
      match uu____5164 with
      | FStar_Syntax_Syntax.Tm_fvar uu____5168 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____5170) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5192) ->
          is_constructed_typ t1 lid
      | uu____5197 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____5206 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____5207 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____5208 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5210) -> get_tycon t2
    | uu____5231 -> FStar_Pervasives_Native.None
  
let (is_interpreted : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    let theory_syms =
      [FStar_Parser_Const.op_Eq;
      FStar_Parser_Const.op_notEq;
      FStar_Parser_Const.op_LT;
      FStar_Parser_Const.op_LTE;
      FStar_Parser_Const.op_GT;
      FStar_Parser_Const.op_GTE;
      FStar_Parser_Const.op_Subtraction;
      FStar_Parser_Const.op_Minus;
      FStar_Parser_Const.op_Addition;
      FStar_Parser_Const.op_Multiply;
      FStar_Parser_Const.op_Division;
      FStar_Parser_Const.op_Modulus;
      FStar_Parser_Const.op_And;
      FStar_Parser_Const.op_Or;
      FStar_Parser_Const.op_Negation]  in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5241 =
      let uu____5242 = un_uinst t  in uu____5242.FStar_Syntax_Syntax.n  in
    match uu____5241 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____5246 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____5251 =
        let uu____5254 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____5254  in
      match uu____5251 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____5267 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (type_u :
  Prims.unit ->
    (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5281  ->
    let u =
      let uu____5287 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____5287
       in
    let uu____5304 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____5304, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____5315 = eq_tm a a'  in
      match uu____5315 with | Equal  -> true | uu____5316 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____5319 =
    let uu____5322 =
      let uu____5323 =
        let uu____5324 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____5324
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____5323  in
    FStar_Syntax_Syntax.mk uu____5322  in
  uu____5319 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    FStar_Pervasives_Native.None
  
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid 
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr 
let (mk_conj_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____5371 =
            let uu____5374 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____5375 =
              let uu____5378 =
                let uu____5379 =
                  let uu____5394 =
                    let uu____5397 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____5398 =
                      let uu____5401 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____5401]  in
                    uu____5397 :: uu____5398  in
                  (tand, uu____5394)  in
                FStar_Syntax_Syntax.Tm_app uu____5379  in
              FStar_Syntax_Syntax.mk uu____5378  in
            uu____5375 FStar_Pervasives_Native.None uu____5374  in
          FStar_Pervasives_Native.Some uu____5371
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____5424 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____5425 =
          let uu____5428 =
            let uu____5429 =
              let uu____5444 =
                let uu____5447 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____5448 =
                  let uu____5451 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____5451]  in
                uu____5447 :: uu____5448  in
              (op_t, uu____5444)  in
            FStar_Syntax_Syntax.Tm_app uu____5429  in
          FStar_Syntax_Syntax.mk uu____5428  in
        uu____5425 FStar_Pervasives_Native.None uu____5424
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____5464 =
      let uu____5467 =
        let uu____5468 =
          let uu____5483 =
            let uu____5486 = FStar_Syntax_Syntax.as_arg phi  in [uu____5486]
             in
          (t_not, uu____5483)  in
        FStar_Syntax_Syntax.Tm_app uu____5468  in
      FStar_Syntax_Syntax.mk uu____5467  in
    uu____5464 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term) =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____5547 =
      let uu____5550 =
        let uu____5551 =
          let uu____5566 =
            let uu____5569 = FStar_Syntax_Syntax.as_arg e  in [uu____5569]
             in
          (b2t_v, uu____5566)  in
        FStar_Syntax_Syntax.Tm_app uu____5551  in
      FStar_Syntax_Syntax.mk uu____5550  in
    uu____5547 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____5583 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____5584 =
        let uu____5587 =
          let uu____5588 =
            let uu____5603 =
              let uu____5606 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____5607 =
                let uu____5610 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____5610]  in
              uu____5606 :: uu____5607  in
            (teq, uu____5603)  in
          FStar_Syntax_Syntax.Tm_app uu____5588  in
        FStar_Syntax_Syntax.mk uu____5587  in
      uu____5584 FStar_Pervasives_Native.None uu____5583
  
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____5629 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____5630 =
            let uu____5633 =
              let uu____5634 =
                let uu____5649 =
                  let uu____5652 = FStar_Syntax_Syntax.iarg t  in
                  let uu____5653 =
                    let uu____5656 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____5657 =
                      let uu____5660 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____5660]  in
                    uu____5656 :: uu____5657  in
                  uu____5652 :: uu____5653  in
                (eq_inst, uu____5649)  in
              FStar_Syntax_Syntax.Tm_app uu____5634  in
            FStar_Syntax_Syntax.mk uu____5633  in
          uu____5630 FStar_Pervasives_Native.None uu____5629
  
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun x  ->
      fun t'  ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid  in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____5683 =
          let uu____5686 =
            let uu____5687 =
              let uu____5702 =
                let uu____5705 = FStar_Syntax_Syntax.iarg t  in
                let uu____5706 =
                  let uu____5709 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____5710 =
                    let uu____5713 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____5713]  in
                  uu____5709 :: uu____5710  in
                uu____5705 :: uu____5706  in
              (t_has_type1, uu____5702)  in
            FStar_Syntax_Syntax.Tm_app uu____5687  in
          FStar_Syntax_Syntax.mk uu____5686  in
        uu____5683 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun t  ->
      fun e  ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____5738 =
          let uu____5741 =
            let uu____5742 =
              let uu____5757 =
                let uu____5760 = FStar_Syntax_Syntax.iarg t  in
                let uu____5761 =
                  let uu____5764 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____5764]  in
                uu____5760 :: uu____5761  in
              (t_with_type1, uu____5757)  in
            FStar_Syntax_Syntax.Tm_app uu____5742  in
          FStar_Syntax_Syntax.mk uu____5741  in
        uu____5738 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____5774 =
    let uu____5777 =
      let uu____5778 =
        let uu____5785 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____5785, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____5778  in
    FStar_Syntax_Syntax.mk uu____5777  in
  uu____5774 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp)
  =
  fun c0  ->
    let uu____5798 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5811 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5822 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____5798 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5843  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let (residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
  
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____5899 =
          let uu____5902 =
            let uu____5903 =
              let uu____5918 =
                let uu____5921 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____5922 =
                  let uu____5925 =
                    let uu____5926 =
                      let uu____5927 =
                        let uu____5928 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____5928]  in
                      abs uu____5927 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____5926  in
                  [uu____5925]  in
                uu____5921 :: uu____5922  in
              (fa, uu____5918)  in
            FStar_Syntax_Syntax.Tm_app uu____5903  in
          FStar_Syntax_Syntax.mk uu____5902  in
        uu____5899 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let (close_forall_no_univs :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____5967 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____5967
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5976 -> true
    | uu____5977 -> false
  
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____6016 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____6016, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____6044 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____6044, FStar_Pervasives_Native.None, t2)  in
        let uu____6057 =
          let uu____6058 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6058  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____6057
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____6128 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6131 =
        let uu____6140 = FStar_Syntax_Syntax.as_arg p  in [uu____6140]  in
      mk_app uu____6128 uu____6131
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____6150 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____6153 =
        let uu____6162 = FStar_Syntax_Syntax.as_arg p  in [uu____6162]  in
      mk_app uu____6150 uu____6153
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6170 = head_and_args t  in
    match uu____6170 with
    | (head1,args) ->
        let uu____6211 =
          let uu____6224 =
            let uu____6225 = un_uinst head1  in
            uu____6225.FStar_Syntax_Syntax.n  in
          (uu____6224, args)  in
        (match uu____6211 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____6242)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____6294 =
                    let uu____6299 =
                      let uu____6300 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____6300]  in
                    FStar_Syntax_Subst.open_term uu____6299 p  in
                  (match uu____6294 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____6329 -> failwith "impossible"  in
                       let uu____6334 =
                         let uu____6335 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____6335
                          in
                       if uu____6334
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____6345 -> FStar_Pervasives_Native.None)
         | uu____6348 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6374 = head_and_args t  in
    match uu____6374 with
    | (head1,args) ->
        let uu____6419 =
          let uu____6432 =
            let uu____6433 = FStar_Syntax_Subst.compress head1  in
            uu____6433.FStar_Syntax_Syntax.n  in
          (uu____6432, args)  in
        (match uu____6419 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6453;
               FStar_Syntax_Syntax.vars = uu____6454;_},u::[]),(t1,uu____6457)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6496 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6526 = head_and_args t  in
    match uu____6526 with
    | (head1,args) ->
        let uu____6571 =
          let uu____6584 =
            let uu____6585 = FStar_Syntax_Subst.compress head1  in
            uu____6585.FStar_Syntax_Syntax.n  in
          (uu____6584, args)  in
        (match uu____6571 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6605;
               FStar_Syntax_Syntax.vars = uu____6606;_},u::[]),(t1,uu____6609)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6648 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6670 = let uu____6685 = unmeta t  in head_and_args uu____6685
       in
    match uu____6670 with
    | (head1,uu____6687) ->
        let uu____6708 =
          let uu____6709 = un_uinst head1  in
          uu____6709.FStar_Syntax_Syntax.n  in
        (match uu____6708 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.squash_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.auto_squash_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.and_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.not_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.imp_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.iff_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.ite_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.exists_lid))
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.forall_lid))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.true_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.false_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq3_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.b2t_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.haseq_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.precedes_lid)
         | uu____6713 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6729 =
      let uu____6742 =
        let uu____6743 = FStar_Syntax_Subst.compress t  in
        uu____6743.FStar_Syntax_Syntax.n  in
      match uu____6742 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6852 =
            let uu____6861 =
              let uu____6862 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____6862  in
            (b, uu____6861)  in
          FStar_Pervasives_Native.Some uu____6852
      | uu____6875 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____6729
      (fun uu____6911  ->
         match uu____6911 with
         | (b,c) ->
             let uu____6946 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____6946 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____6993 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____7016 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7016
  
type qpats = FStar_Syntax_Syntax.args Prims.list[@@deriving show]
type connective =
  | QAll of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | QEx of (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
  FStar_Pervasives_Native.tuple3 
  | BaseConn of (FStar_Ident.lident,FStar_Syntax_Syntax.args)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____7059 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____7095 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____7129 -> false
  
let (__proj__BaseConn__item___0 :
  connective ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____7162) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____7174) ->
          unmeta_monadic t
      | uu____7187 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Parser_Const.true_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.false_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.and_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.or_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.imp_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.iff_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.ite_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.not_lid, (Prims.parse_int "1"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "4"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "2"))]  in
      let aux f2 uu____7265 =
        match uu____7265 with
        | (lid,arity) ->
            let uu____7274 =
              let uu____7289 = unmeta_monadic f2  in head_and_args uu____7289
               in
            (match uu____7274 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____7315 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____7315
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____7390 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____7390)
      | uu____7401 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____7448 = head_and_args t1  in
        match uu____7448 with
        | (t2,args) ->
            let uu____7495 = un_uinst t2  in
            let uu____7496 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____7529  ->
                      match uu____7529 with
                      | (t3,imp) ->
                          let uu____7540 = unascribe t3  in (uu____7540, imp)))
               in
            (uu____7495, uu____7496)
         in
      let rec aux qopt out t1 =
        let uu____7575 = let uu____7592 = flat t1  in (qopt, uu____7592)  in
        match uu____7575 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7619;
                 FStar_Syntax_Syntax.vars = uu____7620;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7623);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7624;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7625;_},uu____7626)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7703;
                 FStar_Syntax_Syntax.vars = uu____7704;_},uu____7705::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7708);
                  FStar_Syntax_Syntax.pos = uu____7709;
                  FStar_Syntax_Syntax.vars = uu____7710;_},uu____7711)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7799;
               FStar_Syntax_Syntax.vars = uu____7800;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7803);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7804;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7805;_},uu____7806)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____7877 =
              let uu____7880 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____7880  in
            aux uu____7877 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7886;
               FStar_Syntax_Syntax.vars = uu____7887;_},uu____7888::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7891);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7892;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7893;_},uu____7894)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____7977 =
              let uu____7980 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____7980  in
            aux uu____7977 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7986) ->
            let bs = FStar_List.rev out  in
            let uu____8020 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____8020 with
             | (bs1,t2) ->
                 let uu____8029 = patterns t2  in
                 (match uu____8029 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____8091 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.parse_int "2"))]
       in
    let destruct_sq_base_conn t =
      let uu____8157 = un_squash t  in
      FStar_Util.bind_opt uu____8157
        (fun t1  ->
           let uu____8173 = head_and_args' t1  in
           match uu____8173 with
           | (hd1,args) ->
               let uu____8206 =
                 let uu____8211 =
                   let uu____8212 = un_uinst hd1  in
                   uu____8212.FStar_Syntax_Syntax.n  in
                 (uu____8211, (FStar_List.length args))  in
               (match uu____8206 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_29) when
                    (_0_29 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_30) when
                    (_0_30 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_31) when
                    (_0_31 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_32) when
                    (_0_32 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_33) when
                    (_0_33 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_34) when
                    (_0_34 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_35) when
                    (_0_35 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_36) when
                    (_0_36 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____8295 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____8318 = un_squash t  in
      FStar_Util.bind_opt uu____8318
        (fun t1  ->
           let uu____8333 = arrow_one t1  in
           match uu____8333 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____8348 =
                 let uu____8349 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____8349  in
               if uu____8348
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____8356 = comp_to_comp_typ_nouniv c  in
                    uu____8356.FStar_Syntax_Syntax.result_typ  in
                  let uu____8357 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____8357
                  then
                    let uu____8360 = patterns q  in
                    match uu____8360 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____8416 =
                       let uu____8417 =
                         let uu____8422 =
                           let uu____8425 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____8426 =
                             let uu____8429 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____8429]  in
                           uu____8425 :: uu____8426  in
                         (FStar_Parser_Const.imp_lid, uu____8422)  in
                       BaseConn uu____8417  in
                     FStar_Pervasives_Native.Some uu____8416))
           | uu____8432 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____8440 = un_squash t  in
      FStar_Util.bind_opt uu____8440
        (fun t1  ->
           let uu____8471 = head_and_args' t1  in
           match uu____8471 with
           | (hd1,args) ->
               let uu____8504 =
                 let uu____8517 =
                   let uu____8518 = un_uinst hd1  in
                   uu____8518.FStar_Syntax_Syntax.n  in
                 (uu____8517, args)  in
               (match uu____8504 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____8533)::(a2,uu____8535)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8570 =
                      let uu____8571 = FStar_Syntax_Subst.compress a2  in
                      uu____8571.FStar_Syntax_Syntax.n  in
                    (match uu____8570 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8578) ->
                         let uu____8605 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____8605 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8644 -> failwith "impossible"  in
                              let uu____8649 = patterns q1  in
                              (match uu____8649 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8716 -> FStar_Pervasives_Native.None)
                | uu____8717 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8738 = destruct_sq_forall phi  in
          (match uu____8738 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8760 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8766 = destruct_sq_exists phi  in
          (match uu____8766 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8788 -> f1)
      | uu____8791 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____8795 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____8795
      (fun uu____8800  ->
         let uu____8801 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____8801
           (fun uu____8806  ->
              let uu____8807 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____8807
                (fun uu____8812  ->
                   let uu____8813 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____8813
                     (fun uu____8818  ->
                        let uu____8819 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____8819
                          (fun uu____8823  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____8829 =
      let uu____8830 = FStar_Syntax_Subst.compress t  in
      uu____8830.FStar_Syntax_Syntax.n  in
    match uu____8829 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8837) ->
        let uu____8864 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____8864 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____8890 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____8890
             then
               let uu____8893 =
                 let uu____8902 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____8902]  in
               mk_app t uu____8893
             else e1)
    | uu____8904 ->
        let uu____8905 =
          let uu____8914 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____8914]  in
        mk_app t uu____8905
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____8925 =
            let uu____8930 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.Delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____8930  in
          let uu____8931 =
            let uu____8932 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____8932  in
          let uu____8935 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____8925 a.FStar_Syntax_Syntax.action_univs uu____8931
            FStar_Parser_Const.effect_Tot_lid uu____8935 [] pos
           in
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_let
               ((false, [lb]), [a.FStar_Syntax_Syntax.action_name]));
          FStar_Syntax_Syntax.sigrng =
            ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.sigquals =
            [FStar_Syntax_Syntax.Visible_default;
            FStar_Syntax_Syntax.Action eff_lid];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = []
        }
  
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____8962 =
      let uu____8965 =
        let uu____8966 =
          let uu____8981 =
            let uu____8984 = FStar_Syntax_Syntax.as_arg t  in [uu____8984]
             in
          (reify_, uu____8981)  in
        FStar_Syntax_Syntax.Tm_app uu____8966  in
      FStar_Syntax_Syntax.mk uu____8965  in
    uu____8962 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____8996 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____9022 = unfold_lazy i  in delta_qualifier uu____9022
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____9024 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____9025 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____9026 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____9049 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____9066 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____9067 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____9074 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____9075 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9089) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____9094;
           FStar_Syntax_Syntax.index = uu____9095;
           FStar_Syntax_Syntax.sort = t2;_},uu____9097)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____9105) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____9111,uu____9112) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____9154) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____9175,t2,uu____9177) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____9198,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____9224 = delta_qualifier t  in incr_delta_depth uu____9224
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____9228 =
      let uu____9229 = FStar_Syntax_Subst.compress t  in
      uu____9229.FStar_Syntax_Syntax.n  in
    match uu____9228 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____9232 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____9244 = let uu____9259 = unmeta e  in head_and_args uu____9259
       in
    match uu____9244 with
    | (head1,args) ->
        let uu____9286 =
          let uu____9299 =
            let uu____9300 = un_uinst head1  in
            uu____9300.FStar_Syntax_Syntax.n  in
          (uu____9299, args)  in
        (match uu____9286 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9316) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____9336::(hd1,uu____9338)::(tl1,uu____9340)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____9387 =
               let uu____9392 =
                 let uu____9397 = list_elements tl1  in
                 FStar_Util.must uu____9397  in
               hd1 :: uu____9392  in
             FStar_Pervasives_Native.Some uu____9387
         | uu____9410 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____9428 .
    ('Auu____9428 -> 'Auu____9428) ->
      'Auu____9428 Prims.list -> 'Auu____9428 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____9451 = f a  in [uu____9451]
      | x::xs -> let uu____9456 = apply_last f xs  in x :: uu____9456
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p
         in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
  
let rec (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____9490 =
            let uu____9493 =
              let uu____9494 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____9494  in
            FStar_Syntax_Syntax.mk uu____9493  in
          uu____9490 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____9507 =
            let uu____9508 =
              let uu____9509 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9509
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9508 args  in
          uu____9507 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____9521 =
            let uu____9522 =
              let uu____9523 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____9523
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____9522 args  in
          uu____9521 FStar_Pervasives_Native.None pos  in
        let uu____9526 =
          let uu____9527 =
            let uu____9528 = FStar_Syntax_Syntax.iarg typ  in [uu____9528]
             in
          nil uu____9527 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____9534 =
                 let uu____9535 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____9536 =
                   let uu____9539 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____9540 =
                     let uu____9543 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____9543]  in
                   uu____9539 :: uu____9540  in
                 uu____9535 :: uu____9536  in
               cons1 uu____9534 t.FStar_Syntax_Syntax.pos) l uu____9526
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____9552 =
        let uu____9555 =
          let uu____9556 =
            let uu____9573 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____9573, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____9556  in
        FStar_Syntax_Syntax.mk uu____9555  in
      uu____9552 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____9633 -> false
  
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Util.either -> ('a,'b) FStar_Util.either -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with
          | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
          | uu____9730 -> false
  
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Pervasives_Native.tuple2 ->
          ('a,'b) FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
  
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1,FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | uu____9868 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____9898 = FStar_ST.op_Bang debug_term_eq  in
          if uu____9898
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
  
let (fail : Prims.string -> Prims.bool) = fun msg  -> check msg false 
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____10030 = unmeta_safe t1  in canon_app uu____10030
           in
        let t21 = let uu____10034 = unmeta_safe t2  in canon_app uu____10034
           in
        let uu____10035 =
          let uu____10040 =
            let uu____10041 =
              let uu____10044 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____10044  in
            uu____10041.FStar_Syntax_Syntax.n  in
          let uu____10045 =
            let uu____10046 =
              let uu____10049 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____10049  in
            uu____10046.FStar_Syntax_Syntax.n  in
          (uu____10040, uu____10045)  in
        match uu____10035 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____10050,uu____10051) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10058,FStar_Syntax_Syntax.Tm_uinst uu____10059) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____10066,uu____10067) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10092,FStar_Syntax_Syntax.Tm_delayed uu____10093) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____10118,uu____10119) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____10146,FStar_Syntax_Syntax.Tm_ascribed uu____10147) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____10180 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____10180
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____10183 = FStar_Const.eq_const c1 c2  in
            check "const" uu____10183
        | (FStar_Syntax_Syntax.Tm_type
           uu____10184,FStar_Syntax_Syntax.Tm_type uu____10185) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____10234 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____10234) &&
              (let uu____10240 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____10240)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____10279 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____10279) &&
              (let uu____10285 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____10285)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____10299 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____10299)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____10346 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____10346) &&
              (let uu____10348 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____10348)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____10433 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____10433) &&
              (let uu____10435 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____10435)
        | (FStar_Syntax_Syntax.Tm_lazy uu____10450,uu____10451) ->
            let uu____10452 =
              let uu____10453 = unlazy t11  in
              term_eq_dbg dbg uu____10453 t21  in
            check "lazy_l" uu____10452
        | (uu____10454,FStar_Syntax_Syntax.Tm_lazy uu____10455) ->
            let uu____10456 =
              let uu____10457 = unlazy t21  in
              term_eq_dbg dbg t11 uu____10457  in
            check "lazy_r" uu____10456
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____10493 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____10493))
              &&
              (let uu____10495 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____10495)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____10497),FStar_Syntax_Syntax.Tm_uvar (u2,uu____10499)) ->
            check "uvar" (u1 = u2)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (check "tm_quoted qi" (qi1 = qi2)) &&
              (let uu____10571 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____10571)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____10598 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____10598) &&
                   (let uu____10600 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____10600)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____10617 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____10617) &&
                    (let uu____10619 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____10619))
                   &&
                   (let uu____10621 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____10621)
             | uu____10622 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____10627) -> fail "unk"
        | (uu____10628,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____10629,uu____10630) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____10631,uu____10632) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____10633,uu____10634) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____10635,uu____10636) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____10637,uu____10638) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____10639,uu____10640) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____10657,uu____10658) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____10671,uu____10672) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____10679,uu____10680) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____10695,uu____10696) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____10719,uu____10720) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____10733,uu____10734) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____10751,uu____10752) ->
            fail "bottom"
        | (uu____10759,FStar_Syntax_Syntax.Tm_bvar uu____10760) ->
            fail "bottom"
        | (uu____10761,FStar_Syntax_Syntax.Tm_name uu____10762) ->
            fail "bottom"
        | (uu____10763,FStar_Syntax_Syntax.Tm_fvar uu____10764) ->
            fail "bottom"
        | (uu____10765,FStar_Syntax_Syntax.Tm_constant uu____10766) ->
            fail "bottom"
        | (uu____10767,FStar_Syntax_Syntax.Tm_type uu____10768) ->
            fail "bottom"
        | (uu____10769,FStar_Syntax_Syntax.Tm_abs uu____10770) ->
            fail "bottom"
        | (uu____10787,FStar_Syntax_Syntax.Tm_arrow uu____10788) ->
            fail "bottom"
        | (uu____10801,FStar_Syntax_Syntax.Tm_refine uu____10802) ->
            fail "bottom"
        | (uu____10809,FStar_Syntax_Syntax.Tm_app uu____10810) ->
            fail "bottom"
        | (uu____10825,FStar_Syntax_Syntax.Tm_match uu____10826) ->
            fail "bottom"
        | (uu____10849,FStar_Syntax_Syntax.Tm_let uu____10850) ->
            fail "bottom"
        | (uu____10863,FStar_Syntax_Syntax.Tm_uvar uu____10864) ->
            fail "bottom"
        | (uu____10881,FStar_Syntax_Syntax.Tm_meta uu____10882) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____10909 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____10909)
          (fun q1  -> fun q2  -> check "arg qual" (q1 = q2)) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____10930 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____10930)
          (fun q1  -> fun q2  -> check "binder qual" (q1 = q2)) b1 b2

and (lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> fail "lcomp"

and (residual_eq_dbg :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> fail "residual"

and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg  ->
    fun c1  ->
      fun c2  ->
        let c11 = comp_to_comp_typ_nouniv c1  in
        let c21 = comp_to_comp_typ_nouniv c2  in
        ((let uu____10950 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____10950) &&
           (let uu____10952 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____10952))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflags -> FStar_Syntax_Syntax.cflags -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax
                                                               FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple3 ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 -> Prims.bool)
  =
  fun dbg  ->
    fun uu____10957  ->
      fun uu____10958  ->
        match (uu____10957, uu____10958) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____11083 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____11083) &&
               (let uu____11085 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____11085))
              &&
              (let uu____11087 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____11126 -> false  in
               check "branch when" uu____11087)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____11144 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____11144) &&
           (let uu____11150 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____11150))
          &&
          (let uu____11152 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____11152)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____11160 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____11160 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11203 ->
        let uu____11228 =
          let uu____11229 = FStar_Syntax_Subst.compress t  in
          sizeof uu____11229  in
        (Prims.parse_int "1") + uu____11228
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____11231 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11231
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____11233 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____11233
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____11240 = sizeof t1  in (FStar_List.length us) + uu____11240
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____11243) ->
        let uu____11264 = sizeof t1  in
        let uu____11265 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11276  ->
                 match uu____11276 with
                 | (bv,uu____11282) ->
                     let uu____11283 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____11283) (Prims.parse_int "0") bs
           in
        uu____11264 + uu____11265
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____11306 = sizeof hd1  in
        let uu____11307 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____11318  ->
                 match uu____11318 with
                 | (arg,uu____11324) ->
                     let uu____11325 = sizeof arg  in acc + uu____11325)
            (Prims.parse_int "0") args
           in
        uu____11306 + uu____11307
    | uu____11326 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____11333 =
        let uu____11334 = un_uinst t  in uu____11334.FStar_Syntax_Syntax.n
         in
      match uu____11333 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____11338 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> Prims.unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____11365 = FStar_Options.set_options t s  in
        match uu____11365 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.strcat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____11373 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____11373 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  