open Prims
let (codegen_fsharp : Prims.unit -> Prims.bool) =
  fun uu____3  ->
    let uu____4 = FStar_Options.codegen ()  in
    uu____4 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
let pruneNones :
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l  ->
    FStar_List.fold_right
      (fun x  ->
         fun ll  ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None  -> ll) l []
  
let (mk_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "mk_range"))
  
let (dummy_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "dummyRange"))
  
let (mlconst_of_const' :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant) =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____49 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____74) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____80) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____81 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____94 ->
          let uu____95 =
            let uu____96 = FStar_Range.string_of_range p  in
            let uu____97 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____96 uu____97
             in
          failwith uu____95
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____105 =
        let uu____106 =
          let uu____107 =
            let uu____118 = FStar_Util.string_of_int i  in
            (uu____118, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____107  in
        FStar_All.pipe_right uu____106
          (fun _0_41  -> FStar_Extraction_ML_Syntax.MLE_Const _0_41)
         in
      FStar_All.pipe_right uu____105
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____133 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42)
         in
      FStar_All.pipe_right uu____133
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____134 =
      let uu____141 =
        let uu____144 =
          let uu____145 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____145 cstr  in
        let uu____146 =
          let uu____149 =
            let uu____150 =
              let uu____151 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____151 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____150 cint  in
          let uu____152 =
            let uu____155 =
              let uu____156 =
                let uu____157 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____157 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____156 cint  in
            let uu____158 =
              let uu____161 =
                let uu____162 =
                  let uu____163 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____163 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____162 cint  in
              let uu____164 =
                let uu____167 =
                  let uu____168 =
                    let uu____169 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____169 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____168 cint  in
                [uu____167]  in
              uu____161 :: uu____164  in
            uu____155 :: uu____158  in
          uu____149 :: uu____152  in
        uu____144 :: uu____146  in
      (mk_range_mle, uu____141)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____134
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____179 ->
          let uu____180 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____180
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____200 =
            FStar_Util.find_opt
              (fun uu____214  ->
                 match uu____214 with | (y,uu____220) -> y = x) subst1
             in
          (match uu____200 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____237 =
            let uu____244 = subst_aux subst1 t1  in
            let uu____245 = subst_aux subst1 t2  in (uu____244, f, uu____245)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____237
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____252 =
            let uu____259 = FStar_List.map (subst_aux subst1) args  in
            (uu____259, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____252
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____267 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____267
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____278  ->
    fun args  ->
      match uu____278 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____291 =
               let uu____292 = FStar_List.zip formals args  in
               subst_aux uu____292 t  in
             FStar_Pervasives_Native.Some uu____291)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____317 = try_subst ts args  in
      match uu____317 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
  
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun uu___61_328  ->
      match uu___61_328 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____337 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____337 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____343 = try_subst ts args  in
               (match uu____343 with
                | FStar_Pervasives_Native.None  ->
                    let uu____348 =
                      let uu____349 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____350 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____351 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____349 uu____350 uu____351
                       in
                    failwith uu____348
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____355 -> FStar_Pervasives_Native.None)
      | uu____358 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____365) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____366 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___62_373  ->
    match uu___62_373 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
  
let (join :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun f  ->
      fun f'  ->
        match (f, f') with
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_PURE
        | uu____383 ->
            let uu____388 =
              let uu____389 = FStar_Range.string_of_range r  in
              let uu____390 = eff_to_string f  in
              let uu____391 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____389
                uu____390 uu____391
               in
            failwith uu____388
  
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu____420  ->
       fun t  ->
         match uu____420 with
         | (uu____426,t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
  
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option[@@deriving
                                                                    show]
let rec (type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if x = y
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____519 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____551 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____558 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____558 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____568;
                     FStar_Extraction_ML_Syntax.loc = uu____569;_}
                   ->
                   let uu____590 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____590
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____606 = type_leq unfold_ty t2 t2'  in
                        (if uu____606
                         then
                           let body1 =
                             let uu____617 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____617
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____622 =
                             let uu____625 =
                               let uu____626 =
                                 let uu____629 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____629
                                  in
                               FStar_All.pipe_left uu____626
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____625  in
                           (true, uu____622)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____658 =
                           let uu____665 =
                             let uu____668 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____668
                              in
                           type_leq_c unfold_ty uu____665 t2 t2'  in
                         match uu____658 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____692 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____692
                               | uu____701 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____709 ->
                   let uu____712 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____712
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____748 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____748
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____764 = unfold_ty t  in
                 match uu____764 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____778 = unfold_ty t'  in
                     (match uu____778 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____800 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____800
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____817,uu____818) ->
              let uu____825 = unfold_ty t  in
              (match uu____825 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____839 -> (false, FStar_Pervasives_Native.None))
          | (uu____844,FStar_Extraction_ML_Syntax.MLTY_Named uu____845) ->
              let uu____852 = unfold_ty t'  in
              (match uu____852 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____866 -> (false, FStar_Pervasives_Native.None))
          | uu____871 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____882 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____882 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___63_920  ->
    match uu___63_920 with
    | (FStar_Util.Inl uu____931,uu____932)::uu____933 -> true
    | uu____956 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____977  ->
    match uu____977 with
    | (ns,n1) ->
        let uu____992 =
          let uu____993 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____993  in
        if uu____992
        then
          let uu____996 =
            let uu____997 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____997  in
          FStar_Pervasives_Native.Some uu____996
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1008 = is_xtuple mlp  in
        (match uu____1008 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1012 -> e)
    | uu____1015 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___64_1022  ->
    match uu___64_1022 with
    | f::uu____1028 ->
        let uu____1031 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1031 with
         | (ns,uu____1041) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1052 -> failwith "impos"
  
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list ->
        (Prims.string,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
  
let (is_xtuple_ty :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1101  ->
    match uu____1101 with
    | (ns,n1) ->
        let uu____1116 =
          let uu____1117 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1117  in
        if uu____1116
        then
          let uu____1120 =
            let uu____1121 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1121  in
          FStar_Pervasives_Native.Some uu____1120
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1132 = is_xtuple_ty mlp  in
        (match uu____1132 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1136 -> t)
    | uu____1139 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1147 = codegen_fsharp ()  in
    if uu____1147
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1157  ->
    match uu____1157 with
    | (ns,n1) ->
        let uu____1170 = codegen_fsharp ()  in
        if uu____1170
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1181 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1181, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1201 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1201
      then true
      else
        (let uu____1203 = unfold_ty t  in
         match uu____1203 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None  -> false)
  
let rec (eraseTypeDeep :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____1223 =
              let uu____1230 = eraseTypeDeep unfold_ty tyd  in
              let uu____1234 = eraseTypeDeep unfold_ty tycd  in
              (uu____1230, etag, uu____1234)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1223
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1245 = erasableType unfold_ty t  in
          if uu____1245
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1250 =
               let uu____1257 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1257, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1250)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1268 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1268
      | uu____1274 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1277 =
    let uu____1280 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1280  in
  FStar_All.pipe_left uu____1277
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
  
let (conjoin :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
  
let (conjoin_opt :
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some x) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
          let uu____1345 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1345
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1355 = FStar_Range.file_of_range r  in (line, uu____1355)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1378,b) ->
        let uu____1380 = doms_and_cod b  in
        (match uu____1380 with | (ds,c) -> ((a :: ds), c))
    | uu____1401 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1411 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1411
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1436,b) ->
        let uu____1438 = uncurry_mlty_fun b  in
        (match uu____1438 with | (args,res) -> ((a :: args), res))
    | uu____1459 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1468 -> true
    | uu____1469 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1476 -> uu____1476
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> Prims.unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1486 =
          let uu____1491 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1491)  in
        FStar_Errors.log_issue r uu____1486
  
type emb_loc =
  | S 
  | R [@@deriving show]
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1495 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1499 -> false 
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mlexpr' ->
          (FStar_Extraction_ML_Syntax.mlexpr,Prims.int,Prims.bool)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun tcenv  ->
    fun fv  ->
      fun t  ->
        fun ml_fv  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant] tcenv t
             in
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top
             in
          let lid_to_name l =
            let uu____1528 =
              let uu____1529 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1529  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1528
             in
          let lid_to_top_name l =
            let uu____1534 =
              let uu____1535 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1535  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1534
             in
          let str_to_name s =
            let uu____1540 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1540  in
          let str_to_top_name s =
            let uu____1545 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1545  in
          let fstar_syn_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
          let fstar_refl_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
          let mk_basic_embedding l s =
            let emb_prefix =
              match l with
              | S  -> fstar_syn_emb_prefix
              | R  -> fstar_refl_emb_prefix  in
            emb_prefix (Prims.strcat "e_" s)  in
          let mk_arrow_embedding arity =
            let uu____1570 =
              let uu____1571 = FStar_Util.string_of_int arity  in
              Prims.strcat "embed_arrow_" uu____1571  in
            fstar_syn_emb_prefix uu____1570  in
          let mk_any_embedding s =
            let uu____1576 =
              let uu____1577 =
                let uu____1584 = fstar_syn_emb_prefix "mk_any_emb"  in
                let uu____1585 =
                  let uu____1588 = str_to_name s  in [uu____1588]  in
                (uu____1584, uu____1585)  in
              FStar_Extraction_ML_Syntax.MLE_App uu____1577  in
            FStar_All.pipe_left w uu____1576  in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let known_type_constructors =
            let uu____1623 =
              let uu____1634 =
                let uu____1645 =
                  let uu____1656 =
                    let uu____1667 =
                      let uu____1676 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      (uu____1676, (Prims.parse_int "0"), "term", R)  in
                    let uu____1677 =
                      let uu____1688 =
                        let uu____1697 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        (uu____1697, (Prims.parse_int "0"), "fv", R)  in
                      let uu____1698 =
                        let uu____1709 =
                          let uu____1718 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          (uu____1718, (Prims.parse_int "0"), "binder", R)
                           in
                        let uu____1719 =
                          let uu____1730 =
                            let uu____1739 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            (uu____1739, (Prims.parse_int "0"), "binders", R)
                             in
                          let uu____1740 =
                            let uu____1751 =
                              let uu____1762 =
                                let uu____1773 =
                                  let uu____1784 =
                                    let uu____1793 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    (uu____1793, (Prims.parse_int "2"),
                                      "tuple2", S)
                                     in
                                  let uu____1794 =
                                    let uu____1805 =
                                      let uu____1814 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp"
                                         in
                                      (uu____1814, (Prims.parse_int "0"),
                                        "exp", R)
                                       in
                                    [uu____1805]  in
                                  uu____1784 :: uu____1794  in
                                (FStar_Parser_Const.option_lid,
                                  (Prims.parse_int "1"), "option", S) ::
                                  uu____1773
                                 in
                              (FStar_Parser_Const.list_lid,
                                (Prims.parse_int "1"), "list", S) ::
                                uu____1762
                               in
                            (FStar_Parser_Const.norm_step_lid,
                              (Prims.parse_int "0"), "norm_step", S) ::
                              uu____1751
                             in
                          uu____1730 :: uu____1740  in
                        uu____1709 :: uu____1719  in
                      uu____1688 :: uu____1698  in
                    uu____1667 :: uu____1677  in
                  (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                    "string", S) :: uu____1656
                   in
                (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"), "unit",
                  S) :: uu____1645
                 in
              (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool", S)
                :: uu____1634
               in
            (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S) ::
              uu____1623
             in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____1947  ->
                 match uu____1947 with
                 | (x,args,uu____1958,uu____1959) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
              known_type_constructors
             in
          let find_env_entry bv uu____1970 =
            match uu____1970 with
            | (bv',uu____1976) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____1996 =
              let uu____1997 = FStar_Syntax_Subst.compress t2  in
              uu____1997.FStar_Syntax_Syntax.n  in
            match uu____1996 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2005 =
                  let uu____2006 =
                    let uu____2011 =
                      FStar_Util.find_opt (find_env_entry bv) env  in
                    FStar_Util.must uu____2011  in
                  FStar_Pervasives_Native.snd uu____2006  in
                FStar_All.pipe_left mk_any_embedding uu____2005
            | FStar_Syntax_Syntax.Tm_refine (x,uu____2027) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3,uu____2033,uu____2034) ->
                mk_embedding env t3
            | uu____2075 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2077 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2077 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2121 =
                       let uu____2122 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2122.FStar_Syntax_Syntax.n  in
                     (match uu____2121 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2126) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2146  ->
                                 match uu____2146 with
                                 | (t4,uu____2152) -> mk_embedding env t4)
                              args
                             in
                          let nm =
                            (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                             in
                          let uu____2154 =
                            let uu____2163 =
                              FStar_Util.find_opt
                                (fun uu____2187  ->
                                   match uu____2187 with
                                   | (x,uu____2197,uu____2198,uu____2199) ->
                                       FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                known_type_constructors
                               in
                            FStar_All.pipe_right uu____2163 FStar_Util.must
                             in
                          (match uu____2154 with
                           | (uu____2226,t_arity,trepr_head,loc_embedding) ->
                               let head2 =
                                 mk_basic_embedding loc_embedding nm  in
                               (match t_arity with
                                | _0_44 when _0_44 = (Prims.parse_int "0") ->
                                    head2
                                | n1 ->
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (head2, arg_embeddings))))
                      | uu____2234 ->
                          let uu____2235 =
                            let uu____2236 =
                              let uu____2237 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2237
                               in
                            NoTacticEmbedding uu____2236  in
                          FStar_Exn.raise uu____2235))
             in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2249 ->
                let args_tail =
                  FStar_Extraction_ML_Syntax.MLP_Var "args_tail"  in
                let mk_cons hd_pat tail_pat =
                  FStar_Extraction_ML_Syntax.MLP_CTor
                    ((["Prims"], "Cons"), [hd_pat; tail_pat])
                   in
                let fst_pat v1 =
                  FStar_Extraction_ML_Syntax.MLP_Tuple
                    [FStar_Extraction_ML_Syntax.MLP_Var v1;
                    FStar_Extraction_ML_Syntax.MLP_Wild]
                   in
                let pattern =
                  FStar_List.fold_right
                    (fun hd_var  -> mk_cons (fst_pat hd_var)) tvar_names
                    args_tail
                   in
                let branch1 =
                  let uu____2286 =
                    let uu____2287 =
                      let uu____2288 =
                        let uu____2295 =
                          let uu____2298 = str_to_name "args_tail"  in
                          [uu____2298]  in
                        (body, uu____2295)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2288  in
                    FStar_All.pipe_left w uu____2287  in
                  (pattern, FStar_Pervasives_Native.None, uu____2286)  in
                let default_branch =
                  let uu____2312 =
                    let uu____2313 =
                      let uu____2314 =
                        let uu____2321 = str_to_name "failwith"  in
                        let uu____2322 =
                          let uu____2325 =
                            let uu____2326 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange))
                               in
                            FStar_All.pipe_left w uu____2326  in
                          [uu____2325]  in
                        (uu____2321, uu____2322)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2314  in
                    FStar_All.pipe_left w uu____2313  in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2312)
                   in
                let body1 =
                  let uu____2332 =
                    let uu____2333 =
                      let uu____2348 = str_to_name "args"  in
                      (uu____2348, [branch1; default_branch])  in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2333  in
                  FStar_All.pipe_left w uu____2332  in
                mk_lam "args" body1
             in
          let uu____2383 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2383 with
          | (bs,c) ->
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let arity = FStar_List.length bs  in
              let uu____2424 =
                let uu____2441 =
                  FStar_Util.prefix_until
                    (fun uu____2475  ->
                       match uu____2475 with
                       | (b,uu____2481) ->
                           let uu____2482 =
                             let uu____2483 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2483.FStar_Syntax_Syntax.n  in
                           (match uu____2482 with
                            | FStar_Syntax_Syntax.Tm_type uu____2486 -> false
                            | uu____2487 -> true)) bs
                   in
                match uu____2441 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2424 with
               | (type_vars,bs1) ->
                   let non_tvar_arity = FStar_List.length bs1  in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____2670 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____2670) type_vars
                      in
                   let tvar_context =
                     FStar_List.map2
                       (fun b  ->
                          fun nm  -> ((FStar_Pervasives_Native.fst b), nm))
                       type_vars tvar_names
                      in
                   let rec aux accum_embeddings env bs2 =
                     match bs2 with
                     | [] ->
                         let arg_unembeddings =
                           FStar_List.rev accum_embeddings  in
                         let res_embedding = mk_embedding env result_typ  in
                         let uu____2756 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____2756
                         then
                           let embed_fun_N =
                             mk_arrow_embedding non_tvar_arity  in
                           let args =
                             let uu____2775 =
                               let uu____2778 =
                                 let uu____2781 = lid_to_top_name fv  in
                                 [uu____2781]  in
                               res_embedding :: uu____2778  in
                             FStar_List.append arg_unembeddings uu____2775
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs = abstract_tvars tvar_names fun_embedding
                              in
                           let uu____2786 =
                             let uu____2793 = mk_lam "_psc" tabs  in
                             (uu____2793, arity, true)  in
                           FStar_Pervasives_Native.Some uu____2786
                         else
                           (let uu____2805 =
                              let uu____2806 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____2806
                                FStar_Parser_Const.effect_TAC_lid
                               in
                            if uu____2805
                            then
                              let h =
                                let uu____2816 =
                                  let uu____2817 =
                                    FStar_Util.string_of_int non_tvar_arity
                                     in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____2817
                                   in
                                str_to_top_name uu____2816  in
                              let tac_fun =
                                let uu____2825 =
                                  let uu____2826 =
                                    let uu____2833 =
                                      let uu____2834 =
                                        let uu____2835 =
                                          FStar_Util.string_of_int
                                            non_tvar_arity
                                           in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____2835
                                         in
                                      str_to_top_name uu____2834  in
                                    let uu____2842 =
                                      let uu____2845 = lid_to_top_name fv  in
                                      [uu____2845]  in
                                    (uu____2833, uu____2842)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2826
                                   in
                                FStar_All.pipe_left w uu____2825  in
                              let tac_lid_app =
                                let uu____2849 =
                                  let uu____2850 =
                                    let uu____2857 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____2857, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2850
                                   in
                                FStar_All.pipe_left w uu____2849  in
                              let psc = str_to_name "psc"  in
                              let all_args = str_to_name "args"  in
                              let args =
                                let uu____2865 =
                                  let uu____2868 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____2868; tac_fun]  in
                                FStar_List.append uu____2865
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding; tac_lid_app; psc])
                                 in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____2870 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args])))
                                       in
                                    mk_lam "args" uu____2870
                                | uu____2873 ->
                                    let uu____2876 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args))
                                       in
                                    abstract_tvars tvar_names uu____2876
                                 in
                              let uu____2879 =
                                let uu____2886 = mk_lam "psc" tabs  in
                                (uu____2886, (arity + (Prims.parse_int "1")),
                                  false)
                                 in
                              FStar_Pervasives_Native.Some uu____2879
                            else
                              (let uu____2900 =
                                 let uu____2901 =
                                   let uu____2902 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____2902
                                    in
                                 NoTacticEmbedding uu____2901  in
                               FStar_Exn.raise uu____2900))
                     | (b,uu____2912)::bs3 ->
                         let uu____2924 =
                           let uu____2927 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____2927 :: accum_embeddings  in
                         aux uu____2924 env bs3
                      in
                   (try aux [] tvar_context bs1
                    with
                    | NoTacticEmbedding msg ->
                        ((let uu____2960 = FStar_Ident.string_of_lid fv  in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____2960 msg);
                         FStar_Pervasives_Native.None)))
  