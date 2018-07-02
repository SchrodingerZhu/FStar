open Prims
let mkForall_fuel' :
  'Auu____9 .
    FStar_Range.range ->
      'Auu____9 ->
        (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
          FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
          FStar_SMTEncoding_Term.term
  =
  fun r  ->
    fun n1  ->
      fun uu____34  ->
        match uu____34 with
        | (pats,vars,body) ->
            let fallback uu____61 =
              FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
            let uu____66 = FStar_Options.unthrottle_inductives ()  in
            if uu____66
            then fallback ()
            else
              (let uu____68 =
                 FStar_SMTEncoding_Env.fresh_fvar "f"
                   FStar_SMTEncoding_Term.Fuel_sort
                  in
               match uu____68 with
               | (fsym,fterm) ->
                   let add_fuel1 tms =
                     FStar_All.pipe_right tms
                       (FStar_List.map
                          (fun p  ->
                             match p.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Var "HasType",args)
                                 ->
                                 FStar_SMTEncoding_Util.mkApp
                                   ("HasTypeFuel", (fterm :: args))
                             | uu____101 -> p))
                      in
                   let pats1 = FStar_List.map add_fuel1 pats  in
                   let body1 =
                     match body.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                         let guard1 =
                           match guard.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.And ,guards) ->
                               let uu____122 = add_fuel1 guards  in
                               FStar_SMTEncoding_Util.mk_and_l uu____122
                           | uu____125 ->
                               let uu____126 = add_fuel1 [guard]  in
                               FStar_All.pipe_right uu____126 FStar_List.hd
                            in
                         FStar_SMTEncoding_Util.mkImp (guard1, body')
                     | uu____131 -> body  in
                   let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                     vars  in
                   FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
      FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
      FStar_SMTEncoding_Term.term)
  = fun r  -> mkForall_fuel' r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____176 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____191 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____198 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____199 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____212 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____231 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____233 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____233 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____251;
             FStar_Syntax_Syntax.vars = uu____252;_},uu____253)
          ->
          let uu____278 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____278 FStar_Option.isNone
      | uu____295 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____306 =
        let uu____307 = FStar_Syntax_Util.un_uinst t  in
        uu____307.FStar_Syntax_Syntax.n  in
      match uu____306 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____310,uu____311,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___342_336  ->
                  match uu___342_336 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____337 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____339 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____339 FStar_Option.isSome
      | uu____356 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____367 = head_normal env t  in
      if uu____367
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses]
          env.FStar_SMTEncoding_Env.tcenv t
  
let (norm :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Env.Beta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
        FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____384 =
      let uu____385 = FStar_Syntax_Syntax.null_binder t  in [uu____385]  in
    let uu____404 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____384 uu____404 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____448 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____448
                | s ->
                    let uu____451 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____451) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'a . Prims.string -> Prims.int -> Prims.int -> FStar_Range.range -> 'a =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____499 =
            let uu____504 =
              let uu____505 = FStar_Util.string_of_int arity  in
              let uu____506 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____505 uu____506
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____504)  in
          FStar_Errors.raise_error uu____499 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____545 = FStar_Util.first_N arity args  in
               match uu____545 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____568 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____568 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___343_577  ->
    match uu___343_577 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____578 -> false
  
let (is_an_eta_expansion :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____624;
                       FStar_SMTEncoding_Term.rng = uu____625;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____648) ->
              let uu____657 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____668 -> false) args (FStar_List.rev xs))
                 in
              if uu____657
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____672,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____676 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____682 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____682))
                 in
              if uu____676
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____686 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____703 'Auu____704 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv,'Auu____703) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____704) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____762  ->
                  match uu____762 with
                  | (x,uu____768) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____776 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____788 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____788) uu____776 tl1
               in
            let uu____791 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____818  ->
                      match uu____818 with
                      | (b,uu____824) ->
                          let uu____825 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____825))
               in
            (match uu____791 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____831) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____845 =
                   let uu____850 =
                     let uu____851 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____851
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____850)
                    in
                 FStar_Errors.log_issue pos uu____845)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
let (as_function_typ :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1126 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1141 ->
            let uu____1148 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1148
        | uu____1149 ->
            if norm1
            then let uu____1150 = whnf env t1  in aux false uu____1150
            else
              (let uu____1152 =
                 let uu____1153 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1154 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1153 uu____1154
                  in
               failwith uu____1152)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1192) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1197 ->
        let uu____1198 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1198)
  
let is_arithmetic_primitive :
  'Auu____1211 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1211 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1233::uu____1234::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1238::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1241 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1264 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1281 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1288 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1288)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1329)::uu____1330::uu____1331::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1382)::uu____1383::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1420 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1735 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1735, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1736 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1736, [])
      | FStar_Const.Const_char c1 ->
          let uu____1739 =
            let uu____1740 =
              let uu____1747 =
                let uu____1750 =
                  let uu____1751 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1751  in
                [uu____1750]  in
              ("FStar.Char.__char_of_int", uu____1747)  in
            FStar_SMTEncoding_Util.mkApp uu____1740  in
          (uu____1739, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1765 =
            let uu____1766 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1766  in
          (uu____1765, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1785) ->
          let uu____1786 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1786, [])
      | FStar_Const.Const_range uu____1787 ->
          let uu____1788 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1788, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1790 =
            let uu____1791 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1791  in
          failwith uu____1790

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,FStar_SMTEncoding_Env.env_t,
          FStar_SMTEncoding_Term.decls_t,FStar_Syntax_Syntax.bv Prims.list)
          FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____1818 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1818
         then
           let uu____1819 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1819
         else ());
        (let uu____1821 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1915  ->
                   fun b  ->
                     match uu____1915 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1996 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____2016 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2016 with
                           | (xxsym,xx,env') ->
                               let uu____2042 =
                                 let uu____2047 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2047 env1 xx
                                  in
                               (match uu____2042 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1996 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1821 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2208 = encode_term t env  in
          match uu____2208 with
          | (t1,decls) ->
              let uu____2219 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2219, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2230 = encode_term t env  in
          match uu____2230 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2245 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2245, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2247 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2247, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2253 = encode_args args_e env  in
        match uu____2253 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2272 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2283 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2283  in
            let binary arg_tms1 =
              let uu____2298 =
                let uu____2299 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2299  in
              let uu____2300 =
                let uu____2301 =
                  let uu____2302 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2302  in
                FStar_SMTEncoding_Term.unboxInt uu____2301  in
              (uu____2298, uu____2300)  in
            let mk_default uu____2310 =
              let uu____2311 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2311 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2373 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2373
              then
                let uu____2374 =
                  let uu____2375 = mk_args ts  in op uu____2375  in
                FStar_All.pipe_right uu____2374 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2410 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2410
              then
                let uu____2411 = binary ts  in
                match uu____2411 with
                | (t1,t2) ->
                    let uu____2418 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2418
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2422 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2422
                 then
                   let uu____2423 =
                     let uu____2424 = binary ts  in op uu____2424  in
                   FStar_All.pipe_right uu____2423
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____2585 =
              let uu____2595 =
                FStar_List.tryFind
                  (fun uu____2619  ->
                     match uu____2619 with
                     | (l,uu____2629) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2595 FStar_Util.must  in
            (match uu____2585 with
             | (uu____2673,op) ->
                 let uu____2685 = op arg_tms  in (uu____2685, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2693 = FStar_List.hd args_e  in
        match uu____2693 with
        | (tm_sz,uu____2701) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2715 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2715 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2723 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2723);
                   t_decls1)
               in
            let uu____2724 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2748::(sz_arg,uu____2750)::uu____2751::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2818 =
                    let uu____2819 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2819  in
                  let uu____2822 =
                    let uu____2825 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2825  in
                  (uu____2818, uu____2822)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2829::(sz_arg,uu____2831)::uu____2832::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2899 =
                    let uu____2900 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2900
                     in
                  failwith uu____2899
              | uu____2907 ->
                  let uu____2922 = FStar_List.tail args_e  in
                  (uu____2922, FStar_Pervasives_Native.None)
               in
            (match uu____2724 with
             | (arg_tms,ext_sz) ->
                 let uu____2937 = encode_args arg_tms env  in
                 (match uu____2937 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2958 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2969 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2969  in
                      let unary_arith arg_tms2 =
                        let uu____2980 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2980  in
                      let binary arg_tms2 =
                        let uu____2995 =
                          let uu____2996 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2996
                           in
                        let uu____2997 =
                          let uu____2998 =
                            let uu____2999 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2999  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2998
                           in
                        (uu____2995, uu____2997)  in
                      let binary_arith arg_tms2 =
                        let uu____3016 =
                          let uu____3017 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3017
                           in
                        let uu____3018 =
                          let uu____3019 =
                            let uu____3020 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3020  in
                          FStar_SMTEncoding_Term.unboxInt uu____3019  in
                        (uu____3016, uu____3018)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3078 =
                          let uu____3079 = mk_args ts  in op uu____3079  in
                        FStar_All.pipe_right uu____3078 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____3211 =
                          let uu____3216 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3216  in
                        let uu____3218 =
                          let uu____3223 =
                            let uu____3224 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3224  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3223  in
                        mk_bv uu____3211 unary uu____3218 arg_tms2  in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____3457 =
                        let uu____3467 =
                          FStar_List.tryFind
                            (fun uu____3491  ->
                               match uu____3491 with
                               | (l,uu____3501) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3467 FStar_Util.must  in
                      (match uu____3457 with
                       | (uu____3547,op) ->
                           let uu____3559 = op arg_tms1  in
                           (uu____3559, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___347_3569 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___347_3569.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___347_3569.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___347_3569.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___347_3569.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___347_3569.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___347_3569.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___347_3569.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___347_3569.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___347_3569.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___347_3569.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3570 = encode_term t env1  in
      match uu____3570 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3591 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3591 with
           | FStar_Pervasives_Native.Some uu____3598 -> (tm, decls)
           | uu____3599 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3606,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3607;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3608;
                                  FStar_SMTEncoding_Term.rng = uu____3609;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3610;
                       FStar_SMTEncoding_Term.freevars = uu____3611;
                       FStar_SMTEncoding_Term.rng = uu____3612;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3640 ->
                    let uu____3641 = encode_formula t env1  in
                    (match uu____3641 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3657 =
                                 let uu____3662 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3662, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3657
                           | uu____3663 ->
                               let uu____3664 =
                                 let uu____3675 =
                                   let uu____3676 =
                                     let uu____3681 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3681, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3676
                                    in
                                 ([[valid_tm]], vars, uu____3675)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3664
                            in
                         let ax =
                           let uu____3691 =
                             let uu____3698 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3698)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3691  in
                         ((let uu____3700 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3700);
                          (tm,
                            (FStar_List.append decls
                               (FStar_List.append decls' [ax])))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3709 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3709
       then
         let uu____3710 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3711 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3712 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3710 uu____3711
           uu____3712
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3718 ->
           let uu____3741 =
             let uu____3742 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3743 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3744 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3745 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3742
               uu____3743 uu____3744 uu____3745
              in
           failwith uu____3741
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3750 =
             let uu____3751 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3752 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3753 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3754 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3751
               uu____3752 uu____3753 uu____3754
              in
           failwith uu____3750
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____3762 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____3762
             then
               let uu____3763 = FStar_Syntax_Print.term_to_string t0  in
               let uu____3764 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____3763
                 uu____3764
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3767 =
             let uu____3768 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3768
              in
           failwith uu____3767
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3775),uu____3776) ->
           let uu____3825 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3833 -> false  in
           if uu____3825
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3848) ->
           let tv =
             let uu____3854 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3854
              in
           ((let uu____3856 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____3856
             then
               let uu____3857 = FStar_Syntax_Print.term_to_string t0  in
               let uu____3858 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____3857
                 uu____3858
             else ());
            (let t1 =
               let uu____3863 =
                 let uu____3874 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____3874]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____3863
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____3900) ->
           encode_term t1
             (let uu___348_3918 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___348_3918.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___348_3918.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___348_3918.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___348_3918.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___348_3918.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___348_3918.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___348_3918.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___348_3918.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___348_3918.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___348_3918.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3920) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3928 = head_redex env t  in
           if uu____3928
           then let uu____3933 = whnf env t  in encode_term uu____3933 env
           else
             (let uu____3935 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3935 with
              | (uu____3944,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3948 ->
                          let uu____3953 =
                            let uu____3954 =
                              let uu____3961 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3962 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3961,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3962)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3954  in
                          [uu____3953]
                      | FStar_SMTEncoding_Term.App (uu____3963,[]) ->
                          let uu____3966 =
                            let uu____3967 =
                              let uu____3974 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3975 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3974,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3975)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3967  in
                          [uu____3966]
                      | uu____3976 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____3978 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3980) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4009 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4009 with
            | (binders1,res) ->
                let uu____4020 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4020
                then
                  let uu____4025 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4025 with
                   | (vars,guards,env',decls,uu____4050) ->
                       let fsym =
                         let uu____4068 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4068, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4071 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___349_4080 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___349_4080.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___349_4080.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___349_4080.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___349_4080.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___349_4080.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___349_4080.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___349_4080.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___349_4080.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___349_4080.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___349_4080.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___349_4080.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___349_4080.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___349_4080.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___349_4080.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___349_4080.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___349_4080.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___349_4080.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___349_4080.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___349_4080.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___349_4080.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___349_4080.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___349_4080.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___349_4080.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___349_4080.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.nocoerce =
                                (uu___349_4080.FStar_TypeChecker_Env.nocoerce);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___349_4080.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___349_4080.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___349_4080.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___349_4080.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___349_4080.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___349_4080.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___349_4080.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___349_4080.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___349_4080.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___349_4080.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___349_4080.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___349_4080.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___349_4080.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___349_4080.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___349_4080.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___349_4080.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___349_4080.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4071 with
                        | (pre_opt,res_t) ->
                            let uu____4091 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4091 with
                             | (res_pred,decls') ->
                                 let uu____4102 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4115 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4115, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4119 =
                                         encode_formula pre env'  in
                                       (match uu____4119 with
                                        | (guard,decls0) ->
                                            let uu____4132 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4132, decls0))
                                    in
                                 (match uu____4102 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4146 =
                                          let uu____4157 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4157)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4146
                                         in
                                      let cvars =
                                        let uu____4173 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4173
                                          (FStar_List.filter
                                             (fun uu____4199  ->
                                                match uu____4199 with
                                                | (x,uu____4205) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____4218 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4218 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4226 =
                                             let uu____4227 =
                                               let uu____4234 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4234)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4227
                                              in
                                           (uu____4226,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4252 =
                                               let uu____4253 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4253
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4252
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4262 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4262
                                             then
                                               let uu____4263 =
                                                 let uu____4264 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4264 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4263
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____4272 =
                                               let uu____4279 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4279)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4272
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____4291 =
                                               let uu____4298 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4298,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4291
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____4311 =
                                               let uu____4318 =
                                                 let uu____4319 =
                                                   let uu____4330 =
                                                     let uu____4331 =
                                                       let uu____4336 =
                                                         let uu____4337 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4337
                                                          in
                                                       (f_has_t, uu____4336)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4331
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4330)
                                                    in
                                                 let uu____4350 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4350 uu____4319  in
                                               (uu____4318,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4311
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4367 =
                                               let uu____4374 =
                                                 let uu____4375 =
                                                   let uu____4386 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4386)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4375
                                                  in
                                               (uu____4374,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4367
                                              in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____4403 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4403);
                                            (t1, t_decls1)))))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       "Non_total_Tm_arrow"
                      in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____4414 =
                       let uu____4421 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4421,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4414  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4431 =
                       let uu____4438 =
                         let uu____4439 =
                           let uu____4450 =
                             let uu____4451 =
                               let uu____4456 =
                                 let uu____4457 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4457
                                  in
                               (f_has_t, uu____4456)  in
                             FStar_SMTEncoding_Util.mkImp uu____4451  in
                           ([[f_has_t]], [fsym], uu____4450)  in
                         let uu____4474 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4474 uu____4439  in
                       (uu____4438, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4431  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4489 ->
           let uu____4496 =
             let uu____4501 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4501 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4508;
                 FStar_Syntax_Syntax.vars = uu____4509;_} ->
                 let uu____4516 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4516 with
                  | (b,f1) ->
                      let uu____4541 =
                        let uu____4542 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4542  in
                      (uu____4541, f1))
             | uu____4557 -> failwith "impossible"  in
           (match uu____4496 with
            | (x,f) ->
                let uu____4568 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4568 with
                 | (base_t,decls) ->
                     let uu____4579 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4579 with
                      | (x1,xtm,env') ->
                          let uu____4593 = encode_formula f env'  in
                          (match uu____4593 with
                           | (refinement,decls') ->
                               let uu____4604 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4604 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____4624 =
                                        let uu____4631 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4638 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4631
                                          uu____4638
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4624
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4679  ->
                                              match uu____4679 with
                                              | (y,uu____4685) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Term.mkForall
                                        t0.FStar_Syntax_Syntax.pos
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____4712 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4712 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4720 =
                                           let uu____4721 =
                                             let uu____4728 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4728)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4721
                                            in
                                         (uu____4720,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4747 =
                                             let uu____4748 =
                                               let uu____4749 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4749
                                                in
                                             Prims.strcat module_name
                                               uu____4748
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4747
                                            in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____4761 =
                                             let uu____4768 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4768)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4761
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____4783 =
                                             let uu____4790 =
                                               let uu____4791 =
                                                 let uu____4802 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4802)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4791
                                                in
                                             (uu____4790,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4783
                                            in
                                         let t_kinding =
                                           let uu____4812 =
                                             let uu____4819 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4819,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4812
                                            in
                                         let t_interp =
                                           let uu____4829 =
                                             let uu____4836 =
                                               let uu____4837 =
                                                 let uu____4848 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4848)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4837
                                                in
                                             (uu____4836,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4829
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4869 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4869);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4871) ->
           let ttm =
             let uu____4889 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4889  in
           let uu____4890 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____4890 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4902 =
                    let uu____4909 =
                      let uu____4910 =
                        let uu____4911 =
                          let uu____4912 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____4912  in
                        FStar_Util.format1 "uvar_typing_%s" uu____4911  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4910
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4909)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4902  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4913 ->
           let uu____4930 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4930 with
            | (head1,args_e) ->
                let uu____4977 =
                  let uu____4992 =
                    let uu____4993 = FStar_Syntax_Subst.compress head1  in
                    uu____4993.FStar_Syntax_Syntax.n  in
                  (uu____4992, args_e)  in
                (match uu____4977 with
                 | uu____5010 when head_redex env head1 ->
                     let uu____5025 = whnf env t  in
                     encode_term uu____5025 env
                 | uu____5026 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5049 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5067) when
                     (Prims.op_Negation
                        env.FStar_SMTEncoding_Env.encoding_quantifier)
                       &&
                       ((FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.forall_lid)
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.exists_lid))
                     -> encode_deeply_embedded_quantifier t0 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____5089;
                       FStar_Syntax_Syntax.vars = uu____5090;_},uu____5091),uu____5092)
                     when
                     (Prims.op_Negation
                        env.FStar_SMTEncoding_Env.encoding_quantifier)
                       &&
                       ((FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.forall_lid)
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.exists_lid))
                     -> encode_deeply_embedded_quantifier t0 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____5118;
                       FStar_Syntax_Syntax.vars = uu____5119;_},uu____5120),
                    (v0,uu____5122)::(v1,uu____5124)::(v2,uu____5126)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5197 = encode_term v0 env  in
                     (match uu____5197 with
                      | (v01,decls0) ->
                          let uu____5208 = encode_term v1 env  in
                          (match uu____5208 with
                           | (v11,decls1) ->
                               let uu____5219 = encode_term v2 env  in
                               (match uu____5219 with
                                | (v21,decls2) ->
                                    let uu____5230 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5230,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5233)::(v1,uu____5235)::(v2,uu____5237)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5304 = encode_term v0 env  in
                     (match uu____5304 with
                      | (v01,decls0) ->
                          let uu____5315 = encode_term v1 env  in
                          (match uu____5315 with
                           | (v11,decls1) ->
                               let uu____5326 = encode_term v2 env  in
                               (match uu____5326 with
                                | (v21,decls2) ->
                                    let uu____5337 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5337,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5339)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5375)::(rng,uu____5377)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5428) ->
                     let e0 =
                       let uu____5450 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5450
                        in
                     ((let uu____5460 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5460
                       then
                         let uu____5461 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5461
                       else ());
                      (let e =
                         let uu____5466 =
                           let uu____5471 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5472 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5471
                             uu____5472
                            in
                         uu____5466 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5483),(arg,uu____5485)::[]) -> encode_term arg env
                 | uu____5520 ->
                     let uu____5535 = encode_args args_e env  in
                     (match uu____5535 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5596 = encode_term head1 env  in
                            match uu____5596 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5668 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5668 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5766  ->
                                                 fun uu____5767  ->
                                                   match (uu____5766,
                                                           uu____5767)
                                                   with
                                                   | ((bv,uu____5797),
                                                      (a,uu____5799)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5829 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5829
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5830 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5830 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5845 =
                                                   let uu____5852 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5861 =
                                                     let uu____5862 =
                                                       let uu____5863 =
                                                         let uu____5864 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5864
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5863
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5862
                                                      in
                                                   (uu____5852,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5861)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5845
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5881 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5881 with
                            | (fname,fuel_args,arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args)
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____5909;
                                   FStar_Syntax_Syntax.vars = uu____5910;_},uu____5911)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____5918;
                                   FStar_Syntax_Syntax.vars = uu____5919;_},uu____5920)
                                ->
                                let uu____5925 =
                                  let uu____5926 =
                                    let uu____5931 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5931
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5926
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5925
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5961 =
                                  let uu____5962 =
                                    let uu____5967 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5967
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5962
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5961
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5996,(FStar_Util.Inl t1,uu____5998),uu____5999)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6046,(FStar_Util.Inr c,uu____6048),uu____6049)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6096 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6117 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6117
                                  in
                               let uu____6118 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6118 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6134;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6135;_},uu____6136)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____6154 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____6231 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6231 with
            | (bs1,body1,opening) ->
                let fallback uu____6256 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      "Tm_abs"
                     in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____6261 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6261, [decl])  in
                let is_impure rc =
                  let uu____6270 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6270 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6282 =
                          let uu____6295 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6295
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6282 with
                         | (t1,uu____6297,uu____6298) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6316 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6316
                  then
                    let uu____6319 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6319
                  else
                    (let uu____6321 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6321
                     then
                       let uu____6324 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6324
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6331 =
                         let uu____6336 =
                           let uu____6337 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6337
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6336)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6331);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6339 =
                       (is_impure rc) &&
                         (let uu____6341 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6341)
                        in
                     if uu____6339
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6348 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6348 with
                        | (vars,guards,envbody,decls,uu____6373) ->
                            let body2 =
                              let uu____6387 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6387
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6389 = encode_term body2 envbody  in
                            (match uu____6389 with
                             | (body3,decls') ->
                                 let uu____6400 =
                                   let uu____6409 = codomain_eff rc  in
                                   match uu____6409 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6428 = encode_term tfun env
                                          in
                                       (match uu____6428 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6400 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____6462 =
                                          let uu____6473 =
                                            let uu____6474 =
                                              let uu____6479 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____6479, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____6474
                                             in
                                          ([], vars, uu____6473)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____6462
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____6501 =
                                              let uu____6508 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____6508
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____6501
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6531 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____6531 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6539 =
                                             let uu____6540 =
                                               let uu____6547 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____6547)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6540
                                              in
                                           (uu____6539,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____6556 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____6556 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____6565 =
                                                    let uu____6566 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____6566 = cache_size
                                                     in
                                                  if uu____6565
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.FStar_SMTEncoding_Env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____6578 =
                                                      let uu____6579 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____6579
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____6578
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____6584 =
                                                    let uu____6591 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____6591)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6584
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____6609 =
                                                        let uu____6610 =
                                                          let uu____6617 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____6617,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6610
                                                         in
                                                      [uu____6609]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____6628 =
                                                    let uu____6635 =
                                                      let uu____6636 =
                                                        let uu____6647 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____6647)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____6636
                                                       in
                                                    (uu____6635,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6628
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____6660 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____6660);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____6661,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____6662;
                          FStar_Syntax_Syntax.lbunivs = uu____6663;
                          FStar_Syntax_Syntax.lbtyp = uu____6664;
                          FStar_Syntax_Syntax.lbeff = uu____6665;
                          FStar_Syntax_Syntax.lbdef = uu____6666;
                          FStar_Syntax_Syntax.lbattrs = uu____6667;
                          FStar_Syntax_Syntax.lbpos = uu____6668;_}::uu____6669),uu____6670)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6700;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6702;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6704;
                FStar_Syntax_Syntax.lbpos = uu____6705;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6729 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise FStar_SMTEncoding_Env.Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_SMTEncoding_Env.env_t ->
            (FStar_Syntax_Syntax.term ->
               FStar_SMTEncoding_Env.env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____6799 =
                let uu____6804 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6804 env  in
              match uu____6799 with
              | (ee1,decls1) ->
                  let uu____6829 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6829 with
                   | (xs,e21) ->
                       let uu____6854 = FStar_List.hd xs  in
                       (match uu____6854 with
                        | (x1,uu____6872) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6878 = encode_body e21 env'  in
                            (match uu____6878 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____6908 =
              let uu____6915 =
                let uu____6916 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6916  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6915  in
            match uu____6908 with
            | (scrsym,scr',env1) ->
                let uu____6924 = encode_term e env1  in
                (match uu____6924 with
                 | (scr,decls) ->
                     let uu____6935 =
                       let encode_branch b uu____6964 =
                         match uu____6964 with
                         | (else_case,decls1) ->
                             let uu____6983 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____6983 with
                              | (p,w,br) ->
                                  let uu____7009 = encode_pat env1 p  in
                                  (match uu____7009 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7046  ->
                                                   match uu____7046 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7053 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7075 =
                                               encode_term w1 env2  in
                                             (match uu____7075 with
                                              | (w2,decls2) ->
                                                  let uu____7088 =
                                                    let uu____7089 =
                                                      let uu____7094 =
                                                        let uu____7095 =
                                                          let uu____7100 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7100)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7095
                                                         in
                                                      (guard, uu____7094)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7089
                                                     in
                                                  (uu____7088, decls2))
                                          in
                                       (match uu____7053 with
                                        | (guard1,decls2) ->
                                            let uu____7115 =
                                              encode_br br env2  in
                                            (match uu____7115 with
                                             | (br1,decls3) ->
                                                 let uu____7128 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7128,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6935 with
                      | (match_tm,decls1) ->
                          let uu____7149 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7149, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____7171 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____7171
       then
         let uu____7172 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7172
       else ());
      (let uu____7174 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7174 with
       | (vars,pat_term) ->
           let uu____7191 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7244  ->
                     fun v1  ->
                       match uu____7244 with
                       | (env1,vars1) ->
                           let uu____7296 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7296 with
                            | (xx,uu____7318,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7191 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7401 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7402 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7403 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7411 = encode_const c env1  in
                      (match uu____7411 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____7419::uu____7420 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____7423 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____7444 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____7444 with
                        | (uu____7451,uu____7452::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____7455 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7488  ->
                                  match uu____7488 with
                                  | (arg,uu____7496) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7502 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____7502))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____7533) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____7564 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____7587 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7631  ->
                                  match uu____7631 with
                                  | (arg,uu____7645) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7651 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____7651))
                         in
                      FStar_All.pipe_right uu____7587 FStar_List.flatten
                   in
                let pat_term1 uu____7681 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____7691 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7739  ->
                fun uu____7740  ->
                  match (uu____7739, uu____7740) with
                  | ((tms,decls),(t,uu____7780)) ->
                      let uu____7807 = encode_term t env  in
                      (match uu____7807 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7691 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7864 = FStar_Syntax_Util.list_elements e  in
        match uu____7864 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7893 =
          let uu____7910 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7910 FStar_Syntax_Util.head_and_args  in
        match uu____7893 with
        | (head1,args) ->
            let uu____7961 =
              let uu____7976 =
                let uu____7977 = FStar_Syntax_Util.un_uinst head1  in
                uu____7977.FStar_Syntax_Syntax.n  in
              (uu____7976, args)  in
            (match uu____7961 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7999,uu____8000)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8052 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____8106 =
            let uu____8123 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8123 FStar_Syntax_Util.head_and_args
             in
          match uu____8106 with
          | (head1,args) ->
              let uu____8170 =
                let uu____8185 =
                  let uu____8186 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8186.FStar_Syntax_Syntax.n  in
                (uu____8185, args)  in
              (match uu____8170 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8205)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8242 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8272 = smt_pat_or t1  in
            (match uu____8272 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8294 = list_elements1 e  in
                 FStar_All.pipe_right uu____8294
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8324 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____8324
                           (FStar_List.map one_pat)))
             | uu____8347 ->
                 let uu____8352 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____8352])
        | uu____8403 ->
            let uu____8406 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____8406]
         in
      let uu____8457 =
        let uu____8472 =
          let uu____8473 = FStar_Syntax_Subst.compress t  in
          uu____8473.FStar_Syntax_Syntax.n  in
        match uu____8472 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____8512 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____8512 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____8547;
                        FStar_Syntax_Syntax.effect_name = uu____8548;
                        FStar_Syntax_Syntax.result_typ = uu____8549;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____8551)::(post,uu____8553)::(pats,uu____8555)::[];
                        FStar_Syntax_Syntax.flags = uu____8556;_}
                      ->
                      let uu____8617 = lemma_pats pats  in
                      (binders1, pre, post, uu____8617)
                  | uu____8628 -> failwith "impos"))
        | uu____8643 -> failwith "Impos"  in
      match uu____8457 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___350_8679 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___350_8679.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___350_8679.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___350_8679.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___350_8679.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___350_8679.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___350_8679.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___350_8679.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___350_8679.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___350_8679.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___350_8679.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____8680 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____8680 with
           | (vars,guards,env2,decls,uu____8705) ->
               let uu____8718 = encode_smt_patterns patterns env2  in
               (match uu____8718 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___351_8751 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___351_8751.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___351_8751.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___351_8751.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___351_8751.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___351_8751.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___351_8751.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___351_8751.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___351_8751.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___351_8751.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___351_8751.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____8752 =
                      let uu____8757 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8757 env3  in
                    (match uu____8752 with
                     | (pre1,decls'') ->
                         let uu____8764 =
                           let uu____8769 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8769 env3  in
                         (match uu____8764 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8779 =
                                let uu____8780 =
                                  let uu____8791 =
                                    let uu____8792 =
                                      let uu____8797 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8797, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8792
                                     in
                                  (pats, vars, uu____8791)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____8780
                                 in
                              (uu____8779, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list,FStar_SMTEncoding_Term.decl
                                                           Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___352_8819 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___352_8819.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___352_8819.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___352_8819.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___352_8819.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___352_8819.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___352_8819.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___352_8819.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___352_8819.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___352_8819.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___352_8819.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____8834 = FStar_Syntax_Util.head_and_args t  in
        match uu____8834 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8897::(x,uu____8899)::(t1,uu____8901)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8968 = encode_term x env1  in
                 (match uu____8968 with
                  | (x1,decls) ->
                      let uu____8979 = encode_term t1 env1  in
                      (match uu____8979 with
                       | (t2,decls') ->
                           let uu____8990 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____8990, (FStar_List.append decls decls'))))
             | uu____8991 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9034  ->
             match uu____9034 with
             | (pats_l1,decls) ->
                 let uu____9079 =
                   FStar_List.fold_right
                     (fun uu____9114  ->
                        fun uu____9115  ->
                          match (uu____9114, uu____9115) with
                          | ((p,uu____9157),(pats1,decls1)) ->
                              let uu____9192 = encode_smt_pattern p  in
                              (match uu____9192 with
                               | (t,d) ->
                                   let uu____9207 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9207 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9224 =
                                            let uu____9229 =
                                              let uu____9230 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9231 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9230 uu____9231
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9229)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9224);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9079 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____9288 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9288
        then
          let uu____9289 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9290 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9289 uu____9290
        else ()  in
      let enc f r l =
        let uu____9329 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____9361 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____9361 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____9329 with
        | (decls,args) ->
            let uu____9392 =
              let uu___353_9393 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___353_9393.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___353_9393.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9392, decls)
         in
      let const_op f r uu____9428 = let uu____9441 = f r  in (uu____9441, [])
         in
      let un_op f l =
        let uu____9464 = FStar_List.hd l  in FStar_All.pipe_left f uu____9464
         in
      let bin_op f uu___344_9484 =
        match uu___344_9484 with
        | t1::t2::[] -> f (t1, t2)
        | uu____9495 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____9535 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____9560  ->
                 match uu____9560 with
                 | (t,uu____9576) ->
                     let uu____9581 = encode_formula t env  in
                     (match uu____9581 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____9535 with
        | (decls,phis) ->
            let uu____9610 =
              let uu___354_9611 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___354_9611.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___354_9611.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9610, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____9674  ->
               match uu____9674 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____9693) -> false
                    | uu____9694 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____9709 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____9709
        else
          (let uu____9723 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____9723 r rf)
         in
      let mk_imp1 r uu___345_9758 =
        match uu___345_9758 with
        | (lhs,uu____9764)::(rhs,uu____9766)::[] ->
            let uu____9807 = encode_formula rhs env  in
            (match uu____9807 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____9822) ->
                      (l1, decls1)
                  | uu____9827 ->
                      let uu____9828 = encode_formula lhs env  in
                      (match uu____9828 with
                       | (l2,decls2) ->
                           let uu____9839 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____9839, (FStar_List.append decls1 decls2)))))
        | uu____9840 -> failwith "impossible"  in
      let mk_ite r uu___346_9867 =
        match uu___346_9867 with
        | (guard,uu____9873)::(_then,uu____9875)::(_else,uu____9877)::[] ->
            let uu____9934 = encode_formula guard env  in
            (match uu____9934 with
             | (g,decls1) ->
                 let uu____9945 = encode_formula _then env  in
                 (match uu____9945 with
                  | (t,decls2) ->
                      let uu____9956 = encode_formula _else env  in
                      (match uu____9956 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9968 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____9997 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____9997  in
      let connectives =
        let uu____10027 =
          let uu____10052 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____10052)  in
        let uu____10095 =
          let uu____10122 =
            let uu____10147 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____10147)  in
          let uu____10190 =
            let uu____10217 =
              let uu____10244 =
                let uu____10269 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____10269)  in
              let uu____10312 =
                let uu____10339 =
                  let uu____10366 =
                    let uu____10391 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____10391)  in
                  [uu____10366;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____10339  in
              uu____10244 :: uu____10312  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____10217  in
          uu____10122 :: uu____10190  in
        uu____10027 :: uu____10095  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____10844 = encode_formula phi' env  in
            (match uu____10844 with
             | (phi2,decls) ->
                 let uu____10855 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____10855, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10856 ->
            let uu____10863 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____10863 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____10902 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____10902 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____10914;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____10916;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____10918;
                 FStar_Syntax_Syntax.lbpos = uu____10919;_}::[]),e2)
            ->
            let uu____10943 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____10943 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10996::(x,uu____10998)::(t,uu____11000)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11067 = encode_term x env  in
                 (match uu____11067 with
                  | (x1,decls) ->
                      let uu____11078 = encode_term t env  in
                      (match uu____11078 with
                       | (t1,decls') ->
                           let uu____11089 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11089, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11092)::(msg,uu____11094)::(phi2,uu____11096)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11163 =
                   let uu____11168 =
                     let uu____11169 = FStar_Syntax_Subst.compress r  in
                     uu____11169.FStar_Syntax_Syntax.n  in
                   let uu____11172 =
                     let uu____11173 = FStar_Syntax_Subst.compress msg  in
                     uu____11173.FStar_Syntax_Syntax.n  in
                   (uu____11168, uu____11172)  in
                 (match uu____11163 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11182))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11188 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11195)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11230 when head_redex env head2 ->
                 let uu____11245 = whnf env phi1  in
                 encode_formula uu____11245 env
             | uu____11246 ->
                 let uu____11261 = encode_term phi1 env  in
                 (match uu____11261 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____11273 =
                          let uu____11274 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____11275 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____11274 uu____11275
                           in
                        if uu____11273
                        then tt
                        else
                          (let uu___355_11277 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___355_11277.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___355_11277.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____11278 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____11278, decls)))
        | uu____11279 ->
            let uu____11280 = encode_term phi1 env  in
            (match uu____11280 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____11292 =
                     let uu____11293 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____11294 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____11293 uu____11294  in
                   if uu____11292
                   then tt
                   else
                     (let uu___356_11296 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___356_11296.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___356_11296.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____11297 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____11297, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____11341 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____11341 with
        | (vars,guards,env2,decls,uu____11380) ->
            let uu____11393 = encode_smt_patterns ps env2  in
            (match uu____11393 with
             | (pats,decls') ->
                 let uu____11436 = encode_formula body env2  in
                 (match uu____11436 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____11468;
                             FStar_SMTEncoding_Term.rng = uu____11469;_}::[])::[]
                            when
                            let uu____11484 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____11484 = gf -> []
                        | uu____11485 -> guards  in
                      let uu____11490 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____11490, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____11501 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____11501 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____11510 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____11616  ->
                     match uu____11616 with
                     | (l,uu____11640) -> FStar_Ident.lid_equals op l))
              in
           (match uu____11510 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____11709,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11801 = encode_q_body env vars pats body  in
             match uu____11801 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____11846 =
                     let uu____11857 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____11857)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____11846
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11888 = encode_q_body env vars pats body  in
             match uu____11888 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____11932 =
                   let uu____11933 =
                     let uu____11944 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____11944)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____11933
                    in
                 (uu____11932, decls))))
