open Prims
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____7 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____7 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))])
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____17 .
    (FStar_Syntax_Syntax.bv,'Auu____17) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.term,'Auu____17) FStar_Pervasives_Native.tuple2
  =
  fun uu____29  ->
    match uu____29 with
    | (b,imp) ->
        let uu____36 = FStar_Syntax_Syntax.bv_to_name b  in (uu____36, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____59 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59
            then []
            else (let uu____71 = arg_of_non_null_binder b  in [uu____71])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple2)
  =
  fun binders  ->
    let uu____95 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____141 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____141
              then
                let b1 =
                  let uu____159 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____159, (FStar_Pervasives_Native.snd b))  in
                let uu____160 = arg_of_non_null_binder b1  in (b1, uu____160)
              else
                (let uu____174 = arg_of_non_null_binder b  in (b, uu____174))))
       in
    FStar_All.pipe_right uu____95 FStar_List.unzip
  
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
              let uu____256 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____256
              then
                let uu____261 = b  in
                match uu____261 with
                | (a,imp) ->
                    let b1 =
                      let uu____269 =
                        let uu____270 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____270  in
                      FStar_Ident.id_of_text uu____269  in
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
        let uu____302 =
          let uu____305 =
            let uu____306 =
              let uu____319 = name_binders binders  in (uu____319, comp)  in
            FStar_Syntax_Syntax.Tm_arrow uu____306  in
          FStar_Syntax_Syntax.mk uu____305  in
        uu____302 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____337 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____377  ->
            match uu____377 with
            | (t,imp) ->
                let uu____388 =
                  let uu____389 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____389
                   in
                (uu____388, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____439  ->
            match uu____439 with
            | (t,imp) ->
                let uu____456 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____456, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____466 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____466
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____475 . 'Auu____475 -> 'Auu____475 Prims.list =
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
          (fun uu____562  ->
             fun uu____563  ->
               match (uu____562, uu____563) with
               | ((x,uu____581),(y,uu____583)) ->
                   let uu____592 =
                     let uu____599 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____599)  in
                   FStar_Syntax_Syntax.NT uu____592) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____605,FStar_Syntax_Syntax.Meta_quoted uu____606) -> e1
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____618) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____624,uu____625) -> unmeta e2
    | uu____666 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____677 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____684 -> e1
         | FStar_Syntax_Syntax.Meta_quoted uu____693 -> e1
         | uu____700 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____702,uu____703) ->
        unmeta_safe e2
    | uu____744 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.universe,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____756 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____757 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____767 = univ_kernel u1  in
        (match uu____767 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____778 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____785 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____793 = univ_kernel u  in FStar_Pervasives_Native.snd uu____793
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____804,uu____805) ->
          failwith "Impossible: compare_univs"
      | (uu____806,FStar_Syntax_Syntax.U_bvar uu____807) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____808) ->
          ~- (Prims.parse_int "1")
      | (uu____809,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____810) -> ~- (Prims.parse_int "1")
      | (uu____811,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____814,FStar_Syntax_Syntax.U_unif
         uu____815) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____824,FStar_Syntax_Syntax.U_name
         uu____825) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____852 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____853 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____852 - uu____853
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____884 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____884
                 (fun uu____899  ->
                    match uu____899 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____913,uu____914) ->
          ~- (Prims.parse_int "1")
      | (uu____917,FStar_Syntax_Syntax.U_max uu____918) ->
          (Prims.parse_int "1")
      | uu____921 ->
          let uu____926 = univ_kernel u1  in
          (match uu____926 with
           | (k1,n1) ->
               let uu____933 = univ_kernel u2  in
               (match uu____933 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____948 = compare_univs u1 u2  in
      uu____948 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      FStar_Syntax_Syntax.mk_Comp
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name =
            (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____973 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____982 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1002 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1011 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c1 =
        match c1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c2 -> c2
        | FStar_Syntax_Syntax.Total (t,u_opt) ->
            let uu____1048 =
              let uu____1049 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____1049  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1048;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____1076 =
              let uu____1077 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____1077  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____1076;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
         in
      let uu___50_1094 = c  in
      let uu____1095 =
        let uu____1096 =
          let uu___51_1097 = comp_to_comp_typ c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___51_1097.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___51_1097.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___51_1097.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___51_1097.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____1096  in
      {
        FStar_Syntax_Syntax.n = uu____1095;
        FStar_Syntax_Syntax.pos = (uu___50_1094.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___50_1094.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____1112 -> c
        | FStar_Syntax_Syntax.GTotal uu____1121 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___52_1132 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___52_1132.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___52_1132.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___52_1132.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___52_1132.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___53_1133 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___53_1133.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___53_1133.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____1136  ->
           let uu____1137 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____1137)
  
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
    | uu____1170 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1179 -> true
    | FStar_Syntax_Syntax.GTotal uu____1188 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___38_1207  ->
               match uu___38_1207 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1208 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___39_1215  ->
               match uu___39_1215 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1216 -> false)))
  
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
            (fun uu___40_1223  ->
               match uu___40_1223 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____1224 -> false)))
  
let (is_tac_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
      FStar_Parser_Const.effect_Tac_lid
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___41_1238  ->
            match uu___41_1238 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1239 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___42_1246  ->
            match uu___42_1246 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____1247 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_tac_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_Ident.lid_equals FStar_Parser_Const.effect_Tac_lid
      (comp_effect_name c)
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1272 -> true
    | FStar_Syntax_Syntax.GTotal uu____1281 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___43_1294  ->
                   match uu___43_1294 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____1295 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___44_1312  ->
               match uu___44_1312 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____1313 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1320 =
      let uu____1321 = FStar_Syntax_Subst.compress t  in
      uu____1321.FStar_Syntax_Syntax.n  in
    match uu____1320 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1324,c) -> is_pure_or_ghost_comp c
    | uu____1342 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1351 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1355 =
      let uu____1356 = FStar_Syntax_Subst.compress t  in
      uu____1356.FStar_Syntax_Syntax.n  in
    match uu____1355 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1359,c) -> is_lemma_comp c
    | uu____1377 -> false
  
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
    | uu____1442 -> (t1, [])
  
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
        let uu____1507 = head_and_args' head1  in
        (match uu____1507 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1564 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1584) ->
        FStar_Syntax_Subst.compress t2
    | uu____1589 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1593 =
      let uu____1594 = FStar_Syntax_Subst.compress t  in
      uu____1594.FStar_Syntax_Syntax.n  in
    match uu____1593 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1597,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1619)::uu____1620 ->
                  let pats' = unmeta pats  in
                  let uu____1664 = head_and_args pats'  in
                  (match uu____1664 with
                   | (head1,uu____1680) ->
                       let uu____1701 =
                         let uu____1702 = un_uinst head1  in
                         uu____1702.FStar_Syntax_Syntax.n  in
                       (match uu____1701 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____1706 -> false))
              | uu____1707 -> false)
         | uu____1716 -> false)
    | uu____1717 -> false
  
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
                (fun uu___45_1729  ->
                   match uu___45_1729 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____1730 -> false)))
    | uu____1731 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1744) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____1754) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____1774 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____1783 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___54_1795 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___54_1795.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___54_1795.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___54_1795.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___54_1795.FStar_Syntax_Syntax.flags)
             })
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___46_1806  ->
            match uu___46_1806 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____1807 -> false))
  
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
    | uu____1823 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1829,uu____1830) ->
        unascribe e2
    | uu____1871 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1919,uu____1920) ->
          ascribe t' k
      | uu____1961 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____1985 =
      let uu____1990 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____1990  in
    uu____1985 i.FStar_Syntax_Syntax.kind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2035 =
      let uu____2036 = FStar_Syntax_Subst.compress t  in
      uu____2036.FStar_Syntax_Syntax.n  in
    match uu____2035 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2040 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____2040
    | uu____2041 -> t
  
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
            let uu____2071 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____2071;
              FStar_Syntax_Syntax.kind = k;
              FStar_Syntax_Syntax.typ = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown [@@deriving show]
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____2075 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____2079 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____2083 -> false
  
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
      let canon_app t =
        let uu____2106 =
          let uu____2119 = unascribe t  in head_and_args' uu____2119  in
        match uu____2106 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args
              FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___47_2149 = if uu___47_2149 then Equal else Unknown  in
      let equal_iff uu___48_2154 = if uu___48_2154 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____2168 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____2176) -> NotEqual
        | (uu____2177,NotEqual ) -> NotEqual
        | (Unknown ,uu____2178) -> Unknown
        | (uu____2179,Unknown ) -> Unknown  in
      let notq t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (uu____2188,FStar_Syntax_Syntax.Meta_quoted uu____2189) -> false
        | uu____2200 -> true  in
      let equal_data f1 args1 f2 args2 =
        let uu____2238 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____2238
        then
          let uu____2242 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____2300  ->
                    match uu____2300 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____2328 = eq_tm a1 a2  in
                        eq_inj acc uu____2328) Equal) uu____2242
        else NotEqual  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____2332,uu____2333) ->
          let uu____2334 = unlazy t11  in eq_tm uu____2334 t21
      | (uu____2335,FStar_Syntax_Syntax.Tm_lazy uu____2336) ->
          let uu____2337 = unlazy t21  in eq_tm t11 uu____2337
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
            (let uu____2355 = FStar_Syntax_Syntax.fv_eq f g  in
             equal_if uu____2355)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____2368 = eq_tm f g  in
          eq_and uu____2368
            (fun uu____2371  ->
               let uu____2372 = eq_univs_list us vs  in equal_if uu____2372)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2373),uu____2374) -> Unknown
      | (uu____2375,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____2376)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____2379 = FStar_Const.eq_const c d  in equal_iff uu____2379
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____2381),FStar_Syntax_Syntax.Tm_uvar (u2,uu____2383)) ->
          let uu____2432 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____2432
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____2477 =
            let uu____2482 =
              let uu____2483 = un_uinst h1  in
              uu____2483.FStar_Syntax_Syntax.n  in
            let uu____2486 =
              let uu____2487 = un_uinst h2  in
              uu____2487.FStar_Syntax_Syntax.n  in
            (uu____2482, uu____2486)  in
          (match uu____2477 with
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
                 (let uu____2499 =
                    let uu____2500 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____2500  in
                  FStar_List.mem uu____2499 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____2501 ->
               let uu____2506 = eq_tm h1 h2  in
               eq_and uu____2506 (fun uu____2508  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____2511 = eq_univs u v1  in equal_if uu____2511
      | (FStar_Syntax_Syntax.Tm_meta (t1',uu____2513),uu____2514) when
          notq t11 -> eq_tm t1' t21
      | (uu____2519,FStar_Syntax_Syntax.Tm_meta (t2',uu____2521)) when
          notq t21 -> eq_tm t11 t2'
      | (FStar_Syntax_Syntax.Tm_meta
         (uu____2526,FStar_Syntax_Syntax.Meta_quoted (t12,uu____2528)),FStar_Syntax_Syntax.Tm_meta
         (uu____2529,FStar_Syntax_Syntax.Meta_quoted (t22,uu____2531))) ->
          eq_tm t12 t22
      | uu____2548 -> Unknown

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____2584)::a11,(b,uu____2587)::b1) ->
          let uu____2641 = eq_tm a b  in
          (match uu____2641 with
           | Equal  -> eq_args a11 b1
           | uu____2642 -> Unknown)
      | uu____2643 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2655) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2661,uu____2662) ->
        unrefine t2
    | uu____2703 -> t1
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2707 =
      let uu____2708 = unrefine t  in uu____2708.FStar_Syntax_Syntax.n  in
    match uu____2707 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2713) -> is_unit t1
    | uu____2718 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2722 =
      let uu____2723 = unrefine t  in uu____2723.FStar_Syntax_Syntax.n  in
    match uu____2722 with
    | FStar_Syntax_Syntax.Tm_type uu____2726 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____2729) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2751) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____2756,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____2774 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____2778 =
      let uu____2779 = FStar_Syntax_Subst.compress e  in
      uu____2779.FStar_Syntax_Syntax.n  in
    match uu____2778 with
    | FStar_Syntax_Syntax.Tm_abs uu____2782 -> true
    | uu____2799 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2803 =
      let uu____2804 = FStar_Syntax_Subst.compress t  in
      uu____2804.FStar_Syntax_Syntax.n  in
    match uu____2803 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2807 -> true
    | uu____2820 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____2826) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2832,uu____2833) ->
        pre_typ t2
    | uu____2874 -> t1
  
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
      let uu____2892 =
        let uu____2893 = un_uinst typ1  in uu____2893.FStar_Syntax_Syntax.n
         in
      match uu____2892 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____2948 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____2972 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2988,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2994,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____3005,uu____3006,uu____3007,uu____3008,uu____3009) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____3019,uu____3020,uu____3021,uu____3022) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____3028,uu____3029,uu____3030,uu____3031,uu____3032) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3038,uu____3039) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3041,uu____3042) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3045 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____3046 -> []
    | FStar_Syntax_Syntax.Sig_main uu____3047 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____3058 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___49_3075  ->
    match uu___49_3075 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____3085 'Auu____3086 .
    ('Auu____3086 FStar_Syntax_Syntax.syntax,'Auu____3085)
      FStar_Pervasives_Native.tuple2 -> FStar_Range.range
  =
  fun uu____3096  ->
    match uu____3096 with | (hd1,uu____3104) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____3113 'Auu____3114 .
    ('Auu____3114 FStar_Syntax_Syntax.syntax,'Auu____3113)
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
          let uu____3234 =
            let uu____3237 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____3237  in
          uu____3234 FStar_Pervasives_Native.None
            (FStar_Ident.range_of_lid l)
      | uu____3241 ->
          let e =
            let uu____3253 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____3253 args  in
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
      let uu____3264 =
        let uu____3269 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____3269, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____3264
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
          let uu____3304 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____3304
          then
            let uu____3305 =
              let uu____3310 =
                let uu____3311 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____3311  in
              let uu____3312 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____3310, uu____3312)  in
            FStar_Ident.mk_ident uu____3305
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___55_3315 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___55_3315.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___55_3315.FStar_Syntax_Syntax.sort)
          }  in
        let uu____3316 = mk_field_projector_name_from_ident lid nm  in
        (uu____3316, y)
  
let (set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit) =
  fun uv  ->
    fun t  ->
      let uu____3323 = FStar_Syntax_Unionfind.find uv  in
      match uu____3323 with
      | FStar_Pervasives_Native.Some uu____3326 ->
          let uu____3327 =
            let uu____3328 =
              let uu____3329 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____3329  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3328  in
          failwith uu____3327
      | uu____3330 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____3401 -> q1 = q2
  
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
              let uu____3432 =
                let uu___56_3433 = rc  in
                let uu____3434 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___56_3433.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____3434;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___56_3433.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____3432
           in
        match bs with
        | [] -> t
        | uu____3445 ->
            let body =
              let uu____3447 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____3447  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs
                (bs',t1,lopt'),FStar_Pervasives_Native.None ) ->
                 let uu____3475 =
                   let uu____3478 =
                     let uu____3479 =
                       let uu____3496 =
                         let uu____3503 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____3503 bs'  in
                       let uu____3514 = close_lopt lopt'  in
                       (uu____3496, t1, uu____3514)  in
                     FStar_Syntax_Syntax.Tm_abs uu____3479  in
                   FStar_Syntax_Syntax.mk uu____3478  in
                 uu____3475 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____3530 ->
                 let uu____3537 =
                   let uu____3540 =
                     let uu____3541 =
                       let uu____3558 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____3559 = close_lopt lopt  in
                       (uu____3558, body, uu____3559)  in
                     FStar_Syntax_Syntax.Tm_abs uu____3541  in
                   FStar_Syntax_Syntax.mk uu____3540  in
                 uu____3537 FStar_Pervasives_Native.None
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
      | uu____3597 ->
          let uu____3604 =
            let uu____3607 =
              let uu____3608 =
                let uu____3621 = FStar_Syntax_Subst.close_binders bs  in
                let uu____3622 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____3621, uu____3622)  in
              FStar_Syntax_Syntax.Tm_arrow uu____3608  in
            FStar_Syntax_Syntax.mk uu____3607  in
          uu____3604 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____3653 =
        let uu____3654 = FStar_Syntax_Subst.compress t  in
        uu____3654.FStar_Syntax_Syntax.n  in
      match uu____3653 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____3680) ->
               let uu____3689 =
                 let uu____3690 = FStar_Syntax_Subst.compress tres  in
                 uu____3690.FStar_Syntax_Syntax.n  in
               (match uu____3689 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____3725 -> t)
           | uu____3726 -> t)
      | uu____3727 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____3736 =
        let uu____3737 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____3737 t.FStar_Syntax_Syntax.pos  in
      let uu____3738 =
        let uu____3741 =
          let uu____3742 =
            let uu____3749 =
              let uu____3750 =
                let uu____3751 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____3751]  in
              FStar_Syntax_Subst.close uu____3750 t  in
            (b, uu____3749)  in
          FStar_Syntax_Syntax.Tm_refine uu____3742  in
        FStar_Syntax_Syntax.mk uu____3741  in
      uu____3738 FStar_Pervasives_Native.None uu____3736
  
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
        let uu____3800 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____3800 with
         | (bs1,c1) ->
             let uu____3817 = is_tot_or_gtot_comp c1  in
             if uu____3817
             then
               let uu____3828 = arrow_formals_comp (comp_result c1)  in
               (match uu____3828 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____3874;
           FStar_Syntax_Syntax.index = uu____3875;
           FStar_Syntax_Syntax.sort = k2;_},uu____3877)
        -> arrow_formals_comp k2
    | uu____3884 ->
        let uu____3885 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3885)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term'
                                                   FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let uu____3911 = arrow_formals_comp k  in
    match uu____3911 with | (bs,c) -> (bs, (comp_result c))
  
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
          let uu____3987 =
            let uu___57_3988 = rc  in
            let uu____3989 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_3988.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____3989;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_3988.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____3987
      | uu____3996 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____4024 =
        let uu____4025 =
          let uu____4028 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____4028  in
        uu____4025.FStar_Syntax_Syntax.n  in
      match uu____4024 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____4066 = aux t2 what  in
          (match uu____4066 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____4126 -> ([], t1, abs_body_lcomp)  in
    let uu____4139 = aux t FStar_Pervasives_Native.None  in
    match uu____4139 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____4181 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____4181 with
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
              -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              {
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = univ_vars;
                FStar_Syntax_Syntax.lbtyp = typ;
                FStar_Syntax_Syntax.lbeff = eff;
                FStar_Syntax_Syntax.lbdef = def;
                FStar_Syntax_Syntax.lbattrs = lbattrs
              }
  
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                let def1 =
                  match (recs, univ_vars) with
                  | (FStar_Pervasives_Native.None ,uu____4306) -> def
                  | (uu____4317,[]) -> def
                  | (FStar_Pervasives_Native.Some fvs,uu____4329) ->
                      let universes =
                        FStar_All.pipe_right univ_vars
                          (FStar_List.map
                             (fun _0_27  -> FStar_Syntax_Syntax.U_name _0_27))
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
                let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1
                   in
                mk_letbinding lbname univ_vars typ1 eff def2 attrs
  
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
            let uu____4429 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____4429 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____4458 ->
            let t' = arrow binders c  in
            let uu____4468 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____4468 with
             | (uvs1,t'1) ->
                 let uu____4487 =
                   let uu____4488 = FStar_Syntax_Subst.compress t'1  in
                   uu____4488.FStar_Syntax_Syntax.n  in
                 (match uu____4487 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____4529 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____4546 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____4551 -> false
  
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
      let uu____4583 =
        let uu____4584 = pre_typ t  in uu____4584.FStar_Syntax_Syntax.n  in
      match uu____4583 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____4588 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____4595 =
        let uu____4596 = pre_typ t  in uu____4596.FStar_Syntax_Syntax.n  in
      match uu____4595 with
      | FStar_Syntax_Syntax.Tm_fvar uu____4599 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____4601) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4623) ->
          is_constructed_typ t1 lid
      | uu____4628 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____4637 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____4638 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____4639 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____4641) -> get_tycon t2
    | uu____4662 -> FStar_Pervasives_Native.None
  
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
  
let (is_fstar_tactics_embed : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4672 =
      let uu____4673 = un_uinst t  in uu____4673.FStar_Syntax_Syntax.n  in
    match uu____4672 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Parser_Const.fstar_refl_embed_lid
    | uu____4677 -> false
  
let (is_fstar_tactics_quote : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4681 =
      let uu____4682 = un_uinst t  in uu____4682.FStar_Syntax_Syntax.n  in
    match uu____4681 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid
    | uu____4686 -> false
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4690 =
      let uu____4691 = un_uinst t  in uu____4691.FStar_Syntax_Syntax.n  in
    match uu____4690 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____4695 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____4702 =
        let uu____4705 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____4705  in
      match uu____4702 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____4718 -> false
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
  fun uu____4732  ->
    let u =
      let uu____4738 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_28  -> FStar_Syntax_Syntax.U_unif _0_28)
        uu____4738
       in
    let uu____4755 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____4755, u)
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____4762 =
    let uu____4765 =
      let uu____4766 =
        let uu____4767 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____4767
          FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____4766  in
    FStar_Syntax_Syntax.mk uu____4765  in
  uu____4762 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid 
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid 
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid 
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid 
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque" 
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
          let uu____4814 =
            let uu____4817 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____4818 =
              let uu____4821 =
                let uu____4822 =
                  let uu____4837 =
                    let uu____4840 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____4841 =
                      let uu____4844 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____4844]  in
                    uu____4840 :: uu____4841  in
                  (tand, uu____4837)  in
                FStar_Syntax_Syntax.Tm_app uu____4822  in
              FStar_Syntax_Syntax.mk uu____4821  in
            uu____4818 FStar_Pervasives_Native.None uu____4817  in
          FStar_Pervasives_Native.Some uu____4814
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____4867 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____4868 =
          let uu____4871 =
            let uu____4872 =
              let uu____4887 =
                let uu____4890 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____4891 =
                  let uu____4894 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____4894]  in
                uu____4890 :: uu____4891  in
              (op_t, uu____4887)  in
            FStar_Syntax_Syntax.Tm_app uu____4872  in
          FStar_Syntax_Syntax.mk uu____4871  in
        uu____4868 FStar_Pervasives_Native.None uu____4867
  
let (mk_neg :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____4907 =
      let uu____4910 =
        let uu____4911 =
          let uu____4926 =
            let uu____4929 = FStar_Syntax_Syntax.as_arg phi  in [uu____4929]
             in
          (t_not, uu____4926)  in
        FStar_Syntax_Syntax.Tm_app uu____4911  in
      FStar_Syntax_Syntax.mk uu____4910  in
    uu____4907 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____4990 =
      let uu____4993 =
        let uu____4994 =
          let uu____5009 =
            let uu____5012 = FStar_Syntax_Syntax.as_arg e  in [uu____5012]
             in
          (b2t_v, uu____5009)  in
        FStar_Syntax_Syntax.Tm_app uu____4994  in
      FStar_Syntax_Syntax.mk uu____4993  in
    uu____4990 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____5026 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____5027 =
        let uu____5030 =
          let uu____5031 =
            let uu____5046 =
              let uu____5049 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____5050 =
                let uu____5053 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____5053]  in
              uu____5049 :: uu____5050  in
            (teq, uu____5046)  in
          FStar_Syntax_Syntax.Tm_app uu____5031  in
        FStar_Syntax_Syntax.mk uu____5030  in
      uu____5027 FStar_Pervasives_Native.None uu____5026
  
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
          let uu____5072 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____5073 =
            let uu____5076 =
              let uu____5077 =
                let uu____5092 =
                  let uu____5095 = FStar_Syntax_Syntax.iarg t  in
                  let uu____5096 =
                    let uu____5099 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____5100 =
                      let uu____5103 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____5103]  in
                    uu____5099 :: uu____5100  in
                  uu____5095 :: uu____5096  in
                (eq_inst, uu____5092)  in
              FStar_Syntax_Syntax.Tm_app uu____5077  in
            FStar_Syntax_Syntax.mk uu____5076  in
          uu____5073 FStar_Pervasives_Native.None uu____5072
  
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
        let uu____5126 =
          let uu____5129 =
            let uu____5130 =
              let uu____5145 =
                let uu____5148 = FStar_Syntax_Syntax.iarg t  in
                let uu____5149 =
                  let uu____5152 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____5153 =
                    let uu____5156 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____5156]  in
                  uu____5152 :: uu____5153  in
                uu____5148 :: uu____5149  in
              (t_has_type1, uu____5145)  in
            FStar_Syntax_Syntax.Tm_app uu____5130  in
          FStar_Syntax_Syntax.mk uu____5129  in
        uu____5126 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____5181 =
          let uu____5184 =
            let uu____5185 =
              let uu____5200 =
                let uu____5203 = FStar_Syntax_Syntax.iarg t  in
                let uu____5204 =
                  let uu____5207 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____5207]  in
                uu____5203 :: uu____5204  in
              (t_with_type1, uu____5200)  in
            FStar_Syntax_Syntax.Tm_app uu____5185  in
          FStar_Syntax_Syntax.mk uu____5184  in
        uu____5181 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) =
  let uu____5217 =
    let uu____5220 =
      let uu____5221 =
        let uu____5228 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.Delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____5228, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____5221  in
    FStar_Syntax_Syntax.mk uu____5220  in
  uu____5217 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____5241 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____5254 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____5265 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____5241 with
    | (eff_name,flags1) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1
          (fun uu____5286  -> c0)
  
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
        let uu____5342 =
          let uu____5345 =
            let uu____5346 =
              let uu____5361 =
                let uu____5364 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____5365 =
                  let uu____5368 =
                    let uu____5369 =
                      let uu____5370 =
                        let uu____5371 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____5371]  in
                      abs uu____5370 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____5369  in
                  [uu____5368]  in
                uu____5364 :: uu____5365  in
              (fa, uu____5361)  in
            FStar_Syntax_Syntax.Tm_app uu____5346  in
          FStar_Syntax_Syntax.mk uu____5345  in
        uu____5342 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____5410 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____5410
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____5419 -> true
    | uu____5420 -> false
  
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
          let uu____5459 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____5459, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____5487 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____5487, FStar_Pervasives_Native.None, t2)  in
        let uu____5500 =
          let uu____5501 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5501  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____5500
  
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
      let uu____5571 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____5574 =
        let uu____5583 = FStar_Syntax_Syntax.as_arg p  in [uu____5583]  in
      mk_app uu____5571 uu____5574
  
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
      let uu____5593 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____5596 =
        let uu____5605 = FStar_Syntax_Syntax.as_arg p  in [uu____5605]  in
      mk_app uu____5593 uu____5596
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5613 = head_and_args t  in
    match uu____5613 with
    | (head1,args) ->
        let uu____5654 =
          let uu____5667 =
            let uu____5668 = un_uinst head1  in
            uu____5668.FStar_Syntax_Syntax.n  in
          (uu____5667, args)  in
        (match uu____5654 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5685)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____5737 =
                    let uu____5742 =
                      let uu____5743 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____5743]  in
                    FStar_Syntax_Subst.open_term uu____5742 p  in
                  (match uu____5737 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5772 -> failwith "impossible"  in
                       let uu____5777 =
                         let uu____5778 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____5778
                          in
                       if uu____5777
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____5788 -> FStar_Pervasives_Native.None)
         | uu____5791 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5817 = head_and_args t  in
    match uu____5817 with
    | (head1,args) ->
        let uu____5862 =
          let uu____5875 =
            let uu____5876 = FStar_Syntax_Subst.compress head1  in
            uu____5876.FStar_Syntax_Syntax.n  in
          (uu____5875, args)  in
        (match uu____5862 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____5896;
               FStar_Syntax_Syntax.vars = uu____5897;_},u::[]),(t1,uu____5900)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____5939 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5969 = head_and_args t  in
    match uu____5969 with
    | (head1,args) ->
        let uu____6014 =
          let uu____6027 =
            let uu____6028 = FStar_Syntax_Subst.compress head1  in
            uu____6028.FStar_Syntax_Syntax.n  in
          (uu____6027, args)  in
        (match uu____6014 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____6048;
               FStar_Syntax_Syntax.vars = uu____6049;_},u::[]),(t1,uu____6052)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____6091 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____6113 = let uu____6128 = unmeta t  in head_and_args uu____6128
       in
    match uu____6113 with
    | (head1,uu____6130) ->
        let uu____6151 =
          let uu____6152 = un_uinst head1  in
          uu____6152.FStar_Syntax_Syntax.n  in
        (match uu____6151 with
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
         | uu____6156 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____6172 =
      let uu____6185 =
        let uu____6186 = FStar_Syntax_Subst.compress t  in
        uu____6186.FStar_Syntax_Syntax.n  in
      match uu____6185 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____6295 =
            let uu____6304 =
              let uu____6305 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____6305  in
            (b, uu____6304)  in
          FStar_Pervasives_Native.Some uu____6295
      | uu____6318 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____6172
      (fun uu____6354  ->
         match uu____6354 with
         | (b,c) ->
             let uu____6389 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____6389 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____6436 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6459 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6459
  
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
    match projectee with | QAll _0 -> true | uu____6502 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____6538 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders,qpats,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____6572 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____6605) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____6617) ->
          unmeta_monadic t
      | uu____6630 -> f2  in
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
      let aux f2 uu____6708 =
        match uu____6708 with
        | (lid,arity) ->
            let uu____6717 =
              let uu____6732 = unmeta_monadic f2  in head_and_args uu____6732
               in
            (match uu____6717 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____6758 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____6758
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____6833 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____6833)
      | uu____6844 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____6891 = head_and_args t1  in
        match uu____6891 with
        | (t2,args) ->
            let uu____6938 = un_uinst t2  in
            let uu____6939 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____6972  ->
                      match uu____6972 with
                      | (t3,imp) ->
                          let uu____6983 = unascribe t3  in (uu____6983, imp)))
               in
            (uu____6938, uu____6939)
         in
      let rec aux qopt out t1 =
        let uu____7018 = let uu____7035 = flat t1  in (qopt, uu____7035)  in
        match uu____7018 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7062;
                 FStar_Syntax_Syntax.vars = uu____7063;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____7066);
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____7067;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____7068;_},uu____7069)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____7146;
                 FStar_Syntax_Syntax.vars = uu____7147;_},uu____7148::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____7151);
                  FStar_Syntax_Syntax.pos = uu____7152;
                  FStar_Syntax_Syntax.vars = uu____7153;_},uu____7154)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7242;
               FStar_Syntax_Syntax.vars = uu____7243;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____7246);
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7247;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7248;_},uu____7249)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____7325;
               FStar_Syntax_Syntax.vars = uu____7326;_},uu____7327::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____7330);
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____7331;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____7332;_},uu____7333)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (FStar_Pervasives_Native.Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____7421) ->
            let bs = FStar_List.rev out  in
            let uu____7455 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____7455 with
             | (bs1,t2) ->
                 let uu____7464 = patterns t2  in
                 (match uu____7464 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____7526 -> FStar_Pervasives_Native.None  in
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
      let uu____7592 = un_squash t  in
      FStar_Util.bind_opt uu____7592
        (fun t1  ->
           let uu____7608 = head_and_args' t1  in
           match uu____7608 with
           | (hd1,args) ->
               let uu____7641 =
                 let uu____7646 =
                   let uu____7647 = un_uinst hd1  in
                   uu____7647.FStar_Syntax_Syntax.n  in
                 (uu____7646, (FStar_List.length args))  in
               (match uu____7641 with
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
                | uu____7730 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____7753 = un_squash t  in
      FStar_Util.bind_opt uu____7753
        (fun t1  ->
           let uu____7768 = arrow_one t1  in
           match uu____7768 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____7783 =
                 let uu____7784 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____7784  in
               if uu____7783
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____7791 = comp_to_comp_typ c  in
                    uu____7791.FStar_Syntax_Syntax.result_typ  in
                  let uu____7792 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____7792
                  then
                    let uu____7795 = patterns q  in
                    match uu____7795 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____7851 =
                       let uu____7852 =
                         let uu____7857 =
                           let uu____7860 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____7861 =
                             let uu____7864 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____7864]  in
                           uu____7860 :: uu____7861  in
                         (FStar_Parser_Const.imp_lid, uu____7857)  in
                       BaseConn uu____7852  in
                     FStar_Pervasives_Native.Some uu____7851))
           | uu____7867 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____7875 = un_squash t  in
      FStar_Util.bind_opt uu____7875
        (fun t1  ->
           let uu____7906 = head_and_args' t1  in
           match uu____7906 with
           | (hd1,args) ->
               let uu____7939 =
                 let uu____7952 =
                   let uu____7953 = un_uinst hd1  in
                   uu____7953.FStar_Syntax_Syntax.n  in
                 (uu____7952, args)  in
               (match uu____7939 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____7968)::(a2,uu____7970)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____8005 =
                      let uu____8006 = FStar_Syntax_Subst.compress a2  in
                      uu____8006.FStar_Syntax_Syntax.n  in
                    (match uu____8005 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____8013) ->
                         let uu____8040 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____8040 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____8079 -> failwith "impossible"  in
                              let uu____8084 = patterns q1  in
                              (match uu____8084 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____8151 -> FStar_Pervasives_Native.None)
                | uu____8152 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____8173 = destruct_sq_forall phi  in
          (match uu____8173 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8195 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____8201 = destruct_sq_exists phi  in
          (match uu____8201 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____8223 -> f1)
      | uu____8226 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____8230 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____8230
      (fun uu____8235  ->
         let uu____8236 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____8236
           (fun uu____8241  ->
              let uu____8242 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____8242
                (fun uu____8247  ->
                   let uu____8248 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____8248
                     (fun uu____8253  ->
                        let uu____8254 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____8254
                          (fun uu____8258  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____8264 =
      let uu____8265 = FStar_Syntax_Subst.compress t  in
      uu____8265.FStar_Syntax_Syntax.n  in
    match uu____8264 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____8272) ->
        let uu____8299 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____8299 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____8325 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____8325
             then
               let uu____8328 =
                 let uu____8337 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____8337]  in
               mk_app t uu____8328
             else e1)
    | uu____8339 ->
        let uu____8340 =
          let uu____8349 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____8349]  in
        mk_app t uu____8340
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____8357 =
          let uu____8362 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational
              FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____8362  in
        let uu____8363 =
          let uu____8364 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ  in
          arrow a.FStar_Syntax_Syntax.action_params uu____8364  in
        let uu____8367 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
           in
        close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____8357
          a.FStar_Syntax_Syntax.action_univs uu____8363
          FStar_Parser_Const.effect_Tot_lid uu____8367 []
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
    let uu____8394 =
      let uu____8397 =
        let uu____8398 =
          let uu____8413 =
            let uu____8416 = FStar_Syntax_Syntax.as_arg t  in [uu____8416]
             in
          (reify_, uu____8413)  in
        FStar_Syntax_Syntax.Tm_app uu____8398  in
      FStar_Syntax_Syntax.mk uu____8397  in
    uu____8394 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____8428 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____8454 = unfold_lazy i  in delta_qualifier uu____8454
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____8456 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____8457 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____8458 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____8481 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____8498 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____8499 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____8500 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8514) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____8519;
           FStar_Syntax_Syntax.index = uu____8520;
           FStar_Syntax_Syntax.sort = t2;_},uu____8522)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____8530) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8536,uu____8537) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____8579) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____8600,t2,uu____8602) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____8623,t2) -> delta_qualifier t2
  
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
    let uu____8649 = delta_qualifier t  in incr_delta_depth uu____8649
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____8653 =
      let uu____8654 = FStar_Syntax_Subst.compress t  in
      uu____8654.FStar_Syntax_Syntax.n  in
    match uu____8653 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____8657 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____8669 = let uu____8684 = unmeta e  in head_and_args uu____8684
       in
    match uu____8669 with
    | (head1,args) ->
        let uu____8711 =
          let uu____8724 =
            let uu____8725 = un_uinst head1  in
            uu____8725.FStar_Syntax_Syntax.n  in
          (uu____8724, args)  in
        (match uu____8711 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8741) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____8761::(hd1,uu____8763)::(tl1,uu____8765)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____8812 =
               let uu____8817 =
                 let uu____8822 = list_elements tl1  in
                 FStar_Util.must uu____8822  in
               hd1 :: uu____8817  in
             FStar_Pervasives_Native.Some uu____8812
         | uu____8835 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____8853 .
    ('Auu____8853 -> 'Auu____8853) ->
      'Auu____8853 Prims.list -> 'Auu____8853 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____8876 = f a  in [uu____8876]
      | x::xs -> let uu____8881 = apply_last f xs  in x :: uu____8881
  
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
          let uu____8917 =
            let uu____8920 =
              let uu____8921 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____8921  in
            FStar_Syntax_Syntax.mk uu____8920  in
          uu____8917 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____8934 =
            let uu____8935 =
              let uu____8936 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8936
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____8935 args  in
          uu____8934 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____8948 =
            let uu____8949 =
              let uu____8950 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____8950
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____8949 args  in
          uu____8948 FStar_Pervasives_Native.None pos  in
        let uu____8953 =
          let uu____8954 =
            let uu____8955 = FStar_Syntax_Syntax.iarg typ  in [uu____8955]
             in
          nil uu____8954 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____8961 =
                 let uu____8962 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____8963 =
                   let uu____8966 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____8967 =
                     let uu____8970 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____8970]  in
                   uu____8966 :: uu____8967  in
                 uu____8962 :: uu____8963  in
               cons1 uu____8961 t.FStar_Syntax_Syntax.pos) l uu____8953
  
let (uvar_from_id :
  Prims.int ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun id1  ->
    fun t  ->
      let uu____8979 =
        let uu____8982 =
          let uu____8983 =
            let uu____9000 = FStar_Syntax_Unionfind.from_id id1  in
            (uu____9000, t)  in
          FStar_Syntax_Syntax.Tm_uvar uu____8983  in
        FStar_Syntax_Syntax.mk uu____8982  in
      uu____8979 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        | uu____9060 -> false
  
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
          | uu____9157 -> false
  
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
        | uu____9295 -> false
  
let rec (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____9410 ->
            let uu____9425 = head_and_args' t  in
            (match uu____9425 with
             | (hd1,args) ->
                 let uu___58_9458 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.pos =
                     (uu___58_9458.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___58_9458.FStar_Syntax_Syntax.vars)
                 })
        | uu____9469 -> t  in
      let t11 = let uu____9473 = unmeta_safe t1  in canon_app uu____9473  in
      let t21 = let uu____9479 = unmeta_safe t2  in canon_app uu____9479  in
      let uu____9482 =
        let uu____9487 =
          let uu____9488 = FStar_Syntax_Subst.compress t11  in
          uu____9488.FStar_Syntax_Syntax.n  in
        let uu____9491 =
          let uu____9492 = FStar_Syntax_Subst.compress t21  in
          uu____9492.FStar_Syntax_Syntax.n  in
        (uu____9487, uu____9491)  in
      match uu____9482 with
      | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
          x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
          FStar_Syntax_Syntax.bv_eq x y
      | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
          FStar_Syntax_Syntax.fv_eq x y
      | (FStar_Syntax_Syntax.Tm_uinst (t12,us1),FStar_Syntax_Syntax.Tm_uinst
         (t22,us2)) -> (eqlist eq_univs us1 us2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
         c2) -> FStar_Const.eq_const c1 c2
      | (FStar_Syntax_Syntax.Tm_type x,FStar_Syntax_Syntax.Tm_type y) ->
          x = y
      | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
         (b2,t22,k2)) -> (eqlist binder_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
         (b2,c2)) -> (eqlist binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Syntax_Syntax.Tm_refine (b1,t12),FStar_Syntax_Syntax.Tm_refine
         (b2,t22)) -> (FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
         (f2,a2)) -> (term_eq f1 f2) && (eqlist arg_eq a1 a2)
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) -> (term_eq t12 t22) && (eqlist branch_eq bs1 bs2)
      | (FStar_Syntax_Syntax.Tm_ascribed
         (t12,uu____9760,uu____9761),uu____9762) -> term_eq t12 t21
      | (uu____9803,FStar_Syntax_Syntax.Tm_ascribed
         (t22,uu____9805,uu____9806)) -> term_eq t11 t22
      | (FStar_Syntax_Syntax.Tm_let
         ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
          ((b1 = b2) && (eqlist letbinding_eq lbs1 lbs2)) &&
            (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____9882),FStar_Syntax_Syntax.Tm_uvar (u2,uu____9884)) ->
          u1 = u2
      | (FStar_Syntax_Syntax.Tm_delayed uu____9943,uu____9944) ->
          failwith "impossible: term_eq did not compress properly"
      | (uu____9969,FStar_Syntax_Syntax.Tm_delayed uu____9970) ->
          failwith "impossible: term_eq did not compress properly"
      | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
         (t22,m2)) ->
          (match (m1, m2) with
           | (FStar_Syntax_Syntax.Meta_monadic
              (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
               (FStar_Ident.lid_equals n1 n2) && (term_eq ty1 ty2)
           | (FStar_Syntax_Syntax.Meta_monadic_lift
              (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
              (s2,t23,ty2)) ->
               ((FStar_Ident.lid_equals s1 s2) &&
                  (FStar_Ident.lid_equals t13 t23))
                 && (term_eq ty1 ty2)
           | uu____10033 -> false)
      | (FStar_Syntax_Syntax.Tm_unknown ,FStar_Syntax_Syntax.Tm_unknown ) ->
          false
      | (uu____10038,uu____10039) -> false

and (arg_eq :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun a1  -> fun a2  -> eqprod term_eq (fun q1  -> fun q2  -> q1 = q2) a1 a2

and (binder_eq :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.bool)
  =
  fun b1  ->
    fun b2  ->
      eqprod
        (fun b11  ->
           fun b21  ->
             term_eq b11.FStar_Syntax_Syntax.sort
               b21.FStar_Syntax_Syntax.sort) (fun q1  -> fun q2  -> q1 = q2)
        b1 b2

and (lcomp_eq :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> false

and (residual_eq :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> false

and (comp_eq :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun c1  ->
    fun c2  ->
      match ((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Total (t1,u1),FStar_Syntax_Syntax.Total (t2,u2))
          -> term_eq t1 t2
      | (FStar_Syntax_Syntax.GTotal (t1,u1),FStar_Syntax_Syntax.GTotal
         (t2,u2)) -> term_eq t1 t2
      | (FStar_Syntax_Syntax.Comp c11,FStar_Syntax_Syntax.Comp c21) ->
          ((((c11.FStar_Syntax_Syntax.comp_univs =
                c21.FStar_Syntax_Syntax.comp_univs)
               &&
               (c11.FStar_Syntax_Syntax.effect_name =
                  c21.FStar_Syntax_Syntax.effect_name))
              &&
              (term_eq c11.FStar_Syntax_Syntax.result_typ
                 c21.FStar_Syntax_Syntax.result_typ))
             &&
             (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args
                c21.FStar_Syntax_Syntax.effect_args))
            &&
            (eq_flags c11.FStar_Syntax_Syntax.flags
               c21.FStar_Syntax_Syntax.flags)
      | (uu____10134,uu____10135) -> false

and (eq_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool)
  = fun f1  -> fun f2  -> true

and (branch_eq :
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
  fun uu____10142  ->
    fun uu____10143  ->
      match (uu____10142, uu____10143) with
      | ((p1,w1,t1),(p2,w2,t2)) ->
          let uu____10266 = FStar_Syntax_Syntax.eq_pat p1 p2  in
          if uu____10266
          then
            (term_eq t1 t2) &&
              ((match (w1, w2) with
                | (FStar_Pervasives_Native.Some
                   x,FStar_Pervasives_Native.Some y) -> term_eq x y
                | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                   ) -> true
                | uu____10307 -> false))
          else false

and (letbinding_eq :
  FStar_Syntax_Syntax.letbinding ->
    FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun lb1  ->
    fun lb2  ->
      (((eqsum FStar_Syntax_Syntax.bv_eq FStar_Syntax_Syntax.fv_eq
           lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
          &&
          (lb1.FStar_Syntax_Syntax.lbunivs = lb2.FStar_Syntax_Syntax.lbunivs))
         &&
         (term_eq lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp))
        &&
        (term_eq lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)

let rec (bottom_fold :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f  in
      let tn =
        let uu____10340 = FStar_Syntax_Subst.compress t  in
        uu____10340.FStar_Syntax_Syntax.n  in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____10366 =
              let uu____10381 = ff f1  in
              let uu____10382 =
                FStar_List.map
                  (fun uu____10401  ->
                     match uu____10401 with
                     | (a,q) -> let uu____10412 = ff a  in (uu____10412, q))
                  args
                 in
              (uu____10381, uu____10382)  in
            FStar_Syntax_Syntax.Tm_app uu____10366
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____10442 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____10442 with
             | (bs1,t') ->
                 let t'' = ff t'  in
                 let uu____10450 =
                   let uu____10467 = FStar_Syntax_Subst.close bs1 t''  in
                   (bs1, uu____10467, k)  in
                 FStar_Syntax_Syntax.Tm_abs uu____10450)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____10494 = let uu____10501 = ff t1  in (uu____10501, us)
               in
            FStar_Syntax_Syntax.Tm_uinst uu____10494
        | uu____10502 -> tn  in
      f
        (let uu___59_10505 = t  in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.pos = (uu___59_10505.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___59_10505.FStar_Syntax_Syntax.vars)
         })
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____10509 ->
        let uu____10534 =
          let uu____10535 = FStar_Syntax_Subst.compress t  in
          sizeof uu____10535  in
        (Prims.parse_int "1") + uu____10534
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____10537 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____10537
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____10539 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____10539
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____10546 = sizeof t1  in (FStar_List.length us) + uu____10546
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____10549) ->
        let uu____10570 = sizeof t1  in
        let uu____10571 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10582  ->
                 match uu____10582 with
                 | (bv,uu____10588) ->
                     let uu____10589 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____10589) (Prims.parse_int "0") bs
           in
        uu____10570 + uu____10571
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____10612 = sizeof hd1  in
        let uu____10613 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____10624  ->
                 match uu____10624 with
                 | (arg,uu____10630) ->
                     let uu____10631 = sizeof arg  in acc + uu____10631)
            (Prims.parse_int "0") args
           in
        uu____10612 + uu____10613
    | uu____10632 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____10639 =
        let uu____10640 = un_uinst t  in uu____10640.FStar_Syntax_Syntax.n
         in
      match uu____10639 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____10644 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> Prims.unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____10661 = FStar_Options.set_options t s  in
        match uu____10661 with
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
          ((let uu____10669 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____10669 FStar_Pervasives.ignore);
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
  