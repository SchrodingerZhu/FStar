open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun a  -> fun b  -> if a > b then a else b 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____70 = let uu____73 = f x  in uu____73 :: acc  in
            aux xs uu____70
         in
      aux l []
  
let map_rev_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux l acc =
          match l with
          | [] -> l2
          | x::xs ->
              let uu____143 = let uu____146 = f x  in uu____146 :: acc  in
              aux xs uu____143
           in
        aux l1 l2
  
let rec map_append :
  'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list =
  fun f  ->
    fun l1  ->
      fun l2  ->
        match l1 with
        | [] -> l2
        | x::xs ->
            let uu____195 = f x  in
            let uu____196 = map_append f xs l2  in uu____195 :: uu____196
  
let rec drop : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun p  ->
    fun l  ->
      match l with
      | [] -> []
      | x::xs ->
          let uu____232 = p x  in if uu____232 then x :: xs else drop p xs
  
let (debug : FStar_TypeChecker_Cfg.cfg -> (unit -> unit) -> unit) =
  fun cfg  ->
    fun f  ->
      let uu____251 =
        let uu____252 = FStar_TypeChecker_Cfg.cfg_env cfg  in
        FStar_TypeChecker_Env.debug uu____252 (FStar_Options.Other "NBE")  in
      if uu____251 then f () else ()
  
let (debug_term : FStar_Syntax_Syntax.term -> unit) =
  fun t  ->
    let uu____259 = FStar_Syntax_Print.term_to_string t  in
    FStar_Util.print1 "%s\n" uu____259
  
let (debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap -> unit) =
  fun m  ->
    FStar_Util.smap_fold m
      (fun k  ->
         fun v1  ->
           fun u  ->
             let uu____276 = FStar_Syntax_Print.sigelt_to_string_short v1  in
             FStar_Util.print2 "%s -> %%s\n" k uu____276) ()
  
let (pickBranch :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_Syntax_Syntax.branch Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_TypeChecker_NBETerm.t Prims.list)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun scrut  ->
      fun branches  ->
        let rec pickBranch_aux scrut1 branches1 branches0 =
          let rec matches_pat scrutinee p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_var bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_wild bv -> FStar_Util.Inl [scrutinee]
            | FStar_Syntax_Syntax.Pat_dot_term uu____381 -> FStar_Util.Inl []
            | FStar_Syntax_Syntax.Pat_constant s ->
                let matches_const c s1 =
                  debug cfg
                    (fun uu____406  ->
                       let uu____407 =
                         FStar_TypeChecker_NBETerm.t_to_string c  in
                       let uu____408 = FStar_Syntax_Print.const_to_string s1
                          in
                       FStar_Util.print2
                         "Testing term %s against pattern %s\n" uu____407
                         uu____408);
                  (match c with
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Unit ) ->
                       s1 = FStar_Const.Const_unit
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Bool b) ->
                       (match s1 with
                        | FStar_Const.Const_bool p1 -> b = p1
                        | uu____411 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Int i) ->
                       (match s1 with
                        | FStar_Const.Const_int
                            (p1,FStar_Pervasives_Native.None ) ->
                            let uu____424 = FStar_BigInt.big_int_of_string p1
                               in
                            i = uu____424
                        | uu____425 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.String (st,uu____427)) ->
                       (match s1 with
                        | FStar_Const.Const_string (p1,uu____429) -> st = p1
                        | uu____430 -> false)
                   | FStar_TypeChecker_NBETerm.Constant
                       (FStar_TypeChecker_NBETerm.Char c1) ->
                       (match s1 with
                        | FStar_Const.Const_char p1 -> c1 = p1
                        | uu____436 -> false)
                   | uu____437 -> false)
                   in
                let uu____438 = matches_const scrutinee s  in
                if uu____438 then FStar_Util.Inl [] else FStar_Util.Inr false
            | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                let rec matches_args out a p1 =
                  match (a, p1) with
                  | ([],[]) -> FStar_Util.Inl out
                  | ((t,uu____559)::rest_a,(p2,uu____562)::rest_p) ->
                      let uu____596 = matches_pat t p2  in
                      (match uu____596 with
                       | FStar_Util.Inl s ->
                           matches_args (FStar_List.append out s) rest_a
                             rest_p
                       | m -> m)
                  | uu____621 -> FStar_Util.Inr false  in
                (match scrutinee with
                 | FStar_TypeChecker_NBETerm.Construct (fv',_us,args_rev) ->
                     let uu____665 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                     if uu____665
                     then matches_args [] (FStar_List.rev args_rev) arg_pats
                     else FStar_Util.Inr false
                 | uu____679 -> FStar_Util.Inr true)
             in
          match branches1 with
          | [] -> failwith "Branch not found"
          | (p,_wopt,e)::branches2 ->
              let uu____748 = matches_pat scrut1 p  in
              (match uu____748 with
               | FStar_Util.Inl matches ->
                   (debug cfg
                      (fun uu____771  ->
                         let uu____772 = FStar_Syntax_Print.pat_to_string p
                            in
                         FStar_Util.print1 "Pattern %s matches\n" uu____772);
                    FStar_Pervasives_Native.Some (e, matches))
               | FStar_Util.Inr (false ) ->
                   pickBranch_aux scrut1 branches2 branches0
               | FStar_Util.Inr (true ) -> FStar_Pervasives_Native.None)
           in
        pickBranch_aux scrut branches branches
  
let rec test_args :
  'Auu____798 .
    (FStar_TypeChecker_NBETerm.t,'Auu____798) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.int -> Prims.bool
  =
  fun ts  ->
    fun cnt  ->
      match ts with
      | [] -> cnt <= (Prims.parse_int "0")
      | t::ts1 ->
          (let uu____843 =
             FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t)
              in
           Prims.op_Negation uu____843) &&
            (test_args ts1 (cnt - (Prims.parse_int "1")))
  
let rec (count_abstractions : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    let uu____849 =
      let uu____850 = FStar_Syntax_Subst.compress t  in
      uu____850.FStar_Syntax_Syntax.n  in
    match uu____849 with
    | FStar_Syntax_Syntax.Tm_delayed uu____853 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____876 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_name uu____877 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_fvar uu____878 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_constant uu____879 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_type uu____880 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_arrow uu____881 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uvar uu____896 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_refine uu____909 -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_unknown  -> (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____917) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____924) ->
        let uu____949 = count_abstractions body  in
        (FStar_List.length xs) + uu____949
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____982 =
          let uu____983 = count_abstractions head1  in
          uu____983 - (FStar_List.length args)  in
        max uu____982 (Prims.parse_int "0")
    | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
        (match branches with
         | [] -> failwith "Branch not found"
         | (uu____1044,uu____1045,e)::bs -> count_abstractions e)
    | FStar_Syntax_Syntax.Tm_let (uu____1094,t1) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1113) -> count_abstractions t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1119,uu____1120) ->
        count_abstractions t1
    | uu____1161 -> (Prims.parse_int "0")
  
let (find_sigelt_in_gamma :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.env ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lid  ->
        let mapper uu____1206 =
          match uu____1206 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.None ) ->
                   FStar_Pervasives_Native.Some elt
               | FStar_Util.Inr (elt,FStar_Pervasives_Native.Some us) ->
                   (debug cfg
                      (fun uu____1289  ->
                         let uu____1290 =
                           FStar_Syntax_Print.univs_to_string us  in
                         FStar_Util.print1
                           "Universes in local declaration: %s\n" uu____1290);
                    FStar_Pervasives_Native.Some elt)
               | uu____1291 -> FStar_Pervasives_Native.None)
           in
        let uu____1306 = FStar_TypeChecker_Env.lookup_qname env lid  in
        FStar_Util.bind_opt uu____1306 mapper
  
let (is_univ : FStar_TypeChecker_NBETerm.t -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ uu____1350 -> true
    | uu____1351 -> false
  
let (un_univ : FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.universe) =
  fun tm  ->
    match tm with
    | FStar_TypeChecker_NBETerm.Univ u -> u
    | uu____1358 -> failwith "Not a universe"
  
let (is_constr_fv : FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun fvar1  ->
    fvar1.FStar_Syntax_Syntax.fv_qual =
      (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (is_constr : FStar_TypeChecker_Env.qninfo -> Prims.bool) =
  fun q  ->
    match q with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (uu____1371,uu____1372,uu____1373,uu____1374,uu____1375,uu____1376);
            FStar_Syntax_Syntax.sigrng = uu____1377;
            FStar_Syntax_Syntax.sigquals = uu____1378;
            FStar_Syntax_Syntax.sigmeta = uu____1379;
            FStar_Syntax_Syntax.sigattrs = uu____1380;_},uu____1381),uu____1382)
        -> true
    | uu____1437 -> false
  
let (translate_univ :
  FStar_TypeChecker_NBETerm.t Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_NBETerm.t)
  =
  fun bs  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar i ->
            let u' = FStar_List.nth bs i  in un_univ u'
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1462 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1462
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1466 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1466
        | FStar_Syntax_Syntax.U_unknown  -> u2
        | FStar_Syntax_Syntax.U_name uu____1469 -> u2
        | FStar_Syntax_Syntax.U_unif uu____1470 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2  in
      let uu____1479 = aux u  in FStar_TypeChecker_NBETerm.Univ uu____1479
  
let (make_rec_env :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_TypeChecker_NBETerm.t Prims.list)
  =
  fun lbs  ->
    fun bs  ->
      let rec aux lbs1 lbs0 bs1 bs0 =
        match lbs1 with
        | [] -> bs1
        | lb::lbs' ->
            let uu____1547 =
              let uu____1550 =
                FStar_TypeChecker_NBETerm.mkAccuRec lb lbs0 bs0  in
              uu____1550 :: bs1  in
            aux lbs' lbs0 uu____1547 bs0
         in
      aux lbs lbs bs bs
  
let (find_let :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option)
  =
  fun lbs  ->
    fun fvar1  ->
      FStar_Util.find_map lbs
        (fun lb  ->
           match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inl uu____1572 -> failwith "find_let : impossible"
           | FStar_Util.Inr name ->
               let uu____1576 = FStar_Syntax_Syntax.fv_eq name fvar1  in
               if uu____1576
               then FStar_Pervasives_Native.Some lb
               else FStar_Pervasives_Native.None)
  
let rec (iapp :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.args -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun f  ->
      fun args  ->
        debug cfg
          (fun uu____1599  ->
             let uu____1600 = FStar_TypeChecker_NBETerm.t_to_string f  in
             let uu____1601 = FStar_TypeChecker_NBETerm.args_to_string args
                in
             FStar_Util.print2 "App : %s @ %s\n" uu____1600 uu____1601);
        (match f with
         | FStar_TypeChecker_NBETerm.Lam (f1,targs,n1) ->
             let m = FStar_List.length args  in
             if m < n1
             then
               let uu____1644 = FStar_List.splitAt m targs  in
               (match uu____1644 with
                | (uu____1678,targs') ->
                    FStar_TypeChecker_NBETerm.Lam
                      (((fun l  ->
                           let uu____1735 =
                             map_append FStar_Pervasives_Native.fst args l
                              in
                           f1 uu____1735)), targs', (n1 - m)))
             else
               if m = n1
               then
                 (let uu____1751 =
                    FStar_List.map FStar_Pervasives_Native.fst args  in
                  f1 uu____1751)
               else
                 (let uu____1759 = FStar_List.splitAt n1 args  in
                  match uu____1759 with
                  | (args1,args') ->
                      let uu____1806 =
                        let uu____1807 =
                          FStar_List.map FStar_Pervasives_Native.fst args1
                           in
                        f1 uu____1807  in
                      iapp cfg uu____1806 args')
         | FStar_TypeChecker_NBETerm.Accu (a,ts) ->
             FStar_TypeChecker_NBETerm.Accu
               (a, (FStar_List.rev_append args ts))
         | FStar_TypeChecker_NBETerm.Construct (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____1926)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____1970 = aux args us ts  in
             (match uu____1970 with
              | (us',ts') ->
                  FStar_TypeChecker_NBETerm.Construct (i, us', ts'))
         | FStar_TypeChecker_NBETerm.FV (i,us,ts) ->
             let rec aux args1 us1 ts1 =
               match args1 with
               | (FStar_TypeChecker_NBETerm.Univ u,uu____2097)::args2 ->
                   aux args2 (u :: us1) ts1
               | a::args2 -> aux args2 us1 (a :: ts1)
               | [] -> (us1, ts1)  in
             let uu____2141 = aux args us ts  in
             (match uu____2141 with
              | (us',ts') -> FStar_TypeChecker_NBETerm.FV (i, us', ts'))
         | FStar_TypeChecker_NBETerm.Constant uu____2180 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Univ uu____2181 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Type_t uu____2182 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Unknown  ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Refinement uu____2183 ->
             failwith "Ill-typed application"
         | FStar_TypeChecker_NBETerm.Arrow uu____2198 ->
             failwith "Ill-typed application")
  
let (app :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t ->
      FStar_TypeChecker_NBETerm.t ->
        FStar_Syntax_Syntax.aqual -> FStar_TypeChecker_NBETerm.t)
  = fun cfg  -> fun f  -> fun x  -> fun q  -> iapp cfg f [(x, q)] 
let rec tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____2279 = f i  in
          let uu____2280 = aux (i + (Prims.parse_int "1"))  in uu____2279 ::
            uu____2280
        else []  in
      aux (Prims.parse_int "0")
  
let rec (translate_fv :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.fv -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun fvar1  ->
        let debug1 = debug cfg  in
        let qninfo =
          let uu____2414 = FStar_TypeChecker_Cfg.cfg_env cfg  in
          let uu____2415 = FStar_Syntax_Syntax.lid_of_fv fvar1  in
          FStar_TypeChecker_Env.lookup_qname uu____2414 uu____2415  in
        let uu____2416 = (is_constr qninfo) || (is_constr_fv fvar1)  in
        if uu____2416
        then FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] []
        else
          (let uu____2422 =
             FStar_TypeChecker_Normalize.should_unfold cfg
               (fun uu____2424  -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1
               qninfo
              in
           match uu____2422 with
           | FStar_TypeChecker_Normalize.Should_unfold_fully  ->
               failwith "Not yet handled"
           | FStar_TypeChecker_Normalize.Should_unfold_no  ->
               (debug1
                  (fun uu____2430  ->
                     let uu____2431 = FStar_Syntax_Print.fv_to_string fvar1
                        in
                     FStar_Util.print1 "(1) Decided to not unfold %s\n"
                       uu____2431);
                (let uu____2432 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fvar1  in
                 match uu____2432 with
                 | FStar_Pervasives_Native.Some prim_step when
                     prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok ->
                     let arity =
                       prim_step.FStar_TypeChecker_Cfg.arity +
                         prim_step.FStar_TypeChecker_Cfg.univ_arity
                        in
                     let uu____2437 =
                       let uu____2458 =
                         let f uu____2481 uu____2482 =
                           ((FStar_TypeChecker_NBETerm.Constant
                               FStar_TypeChecker_NBETerm.Unit),
                             FStar_Pervasives_Native.None)
                            in
                         tabulate arity f  in
                       ((fun args  ->
                           let args' =
                             FStar_List.map FStar_TypeChecker_NBETerm.as_arg
                               args
                              in
                           let uu____2527 =
                             prim_step.FStar_TypeChecker_Cfg.interpretation_nbe
                               args'
                              in
                           match uu____2527 with
                           | FStar_Pervasives_Native.Some x ->
                               (debug1
                                  (fun uu____2538  ->
                                     let uu____2539 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     let uu____2540 =
                                       FStar_TypeChecker_NBETerm.t_to_string
                                         x
                                        in
                                     FStar_Util.print2
                                       "Primitive operator %s returned %s\n"
                                       uu____2539 uu____2540);
                                x)
                           | FStar_Pervasives_Native.None  ->
                               (debug1
                                  (fun uu____2546  ->
                                     let uu____2547 =
                                       FStar_Syntax_Print.fv_to_string fvar1
                                        in
                                     FStar_Util.print1
                                       "Primitive operator %s failed\n"
                                       uu____2547);
                                (let uu____2548 =
                                   FStar_TypeChecker_NBETerm.mkFV fvar1 [] []
                                    in
                                 iapp cfg uu____2548 args'))), uu____2458,
                         arity)
                        in
                     FStar_TypeChecker_NBETerm.Lam uu____2437
                 | uu____2553 ->
                     (debug1
                        (fun uu____2561  ->
                           let uu____2562 =
                             FStar_Syntax_Print.fv_to_string fvar1  in
                           FStar_Util.print1 "(2) Decided to not unfold %s\n"
                             uu____2562);
                      FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])))
           | FStar_TypeChecker_Normalize.Should_unfold_reify  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2570;
                        FStar_Syntax_Syntax.sigquals = uu____2571;
                        FStar_Syntax_Syntax.sigmeta = uu____2572;
                        FStar_Syntax_Syntax.sigattrs = uu____2573;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2642  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2650  ->
                                 let uu____2651 =
                                   let uu____2652 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2652
                                    in
                                 let uu____2653 =
                                   let uu____2654 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2654
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2651 uu____2653);
                            debug1
                              (fun uu____2662  ->
                                 let uu____2663 =
                                   let uu____2664 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2664
                                    in
                                 let uu____2665 =
                                   let uu____2666 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2666
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2663 uu____2665);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2667 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
           | FStar_TypeChecker_Normalize.Should_unfold_yes  ->
               (match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),names1);
                        FStar_Syntax_Syntax.sigrng = uu____2675;
                        FStar_Syntax_Syntax.sigquals = uu____2676;
                        FStar_Syntax_Syntax.sigmeta = uu____2677;
                        FStar_Syntax_Syntax.sigattrs = uu____2678;_},_us_opt),_rng)
                    ->
                    let lbm = find_let lbs fvar1  in
                    (match lbm with
                     | FStar_Pervasives_Native.Some lb ->
                         if is_rec
                         then FStar_TypeChecker_NBETerm.mkAccuRec lb [] []
                         else
                           (debug1
                              (fun uu____2747  ->
                                 FStar_Util.print
                                   "Translate fv: it's a Sig_let\n" []);
                            debug1
                              (fun uu____2755  ->
                                 let uu____2756 =
                                   let uu____2757 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2757
                                    in
                                 let uu____2758 =
                                   let uu____2759 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbtyp
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2759
                                    in
                                 FStar_Util.print2 "Type of lbdef: %s - %s\n"
                                   uu____2756 uu____2758);
                            debug1
                              (fun uu____2767  ->
                                 let uu____2768 =
                                   let uu____2769 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.tag_of_term uu____2769
                                    in
                                 let uu____2770 =
                                   let uu____2771 =
                                     FStar_Syntax_Subst.compress
                                       lb.FStar_Syntax_Syntax.lbdef
                                      in
                                   FStar_Syntax_Print.term_to_string
                                     uu____2771
                                    in
                                 FStar_Util.print2 "Body of lbdef: %s - %s\n"
                                   uu____2768 uu____2770);
                            translate_letbinding cfg [] lb)
                     | FStar_Pervasives_Native.None  ->
                         failwith "Could not find let binding")
                | uu____2772 -> FStar_TypeChecker_NBETerm.mkFV fvar1 [] []))

and (translate_letbinding :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.letbinding -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun lb  ->
        let debug1 = debug cfg  in
        let us = lb.FStar_Syntax_Syntax.lbunivs  in
        let id1 x = x  in
        let uu____2817 =
          let uu____2838 =
            FStar_List.map
              (fun uu____2859  ->
                 fun uu____2860  ->
                   FStar_All.pipe_left id1
                     ((FStar_TypeChecker_NBETerm.Constant
                         FStar_TypeChecker_NBETerm.Unit),
                       FStar_Pervasives_Native.None)) us
             in
          ((fun us1  ->
              translate cfg (FStar_List.rev_append us1 bs)
                lb.FStar_Syntax_Syntax.lbdef), uu____2838,
            (FStar_List.length us))
           in
        FStar_TypeChecker_NBETerm.Lam uu____2817

and (translate_constant :
  FStar_Syntax_Syntax.sconst -> FStar_TypeChecker_NBETerm.constant) =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_TypeChecker_NBETerm.Unit
    | FStar_Const.Const_bool b -> FStar_TypeChecker_NBETerm.Bool b
    | FStar_Const.Const_int (s,FStar_Pervasives_Native.None ) ->
        let uu____2906 = FStar_BigInt.big_int_of_string s  in
        FStar_TypeChecker_NBETerm.Int uu____2906
    | FStar_Const.Const_string (s,r) ->
        FStar_TypeChecker_NBETerm.String (s, r)
    | FStar_Const.Const_char c1 -> FStar_TypeChecker_NBETerm.Char c1
    | FStar_Const.Const_range r -> FStar_TypeChecker_NBETerm.Range r
    | uu____2912 ->
        let uu____2913 =
          let uu____2914 =
            let uu____2915 = FStar_Syntax_Print.const_to_string c  in
            Prims.strcat uu____2915 ": Not yet implemented"  in
          Prims.strcat "Tm_constant " uu____2914  in
        failwith uu____2913

and (translate_pat :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.pat -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun p  ->
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant c ->
          let uu____2919 = translate_constant c  in
          FStar_TypeChecker_NBETerm.Constant uu____2919
      | FStar_Syntax_Syntax.Pat_cons (cfv,pats) ->
          let uu____2938 = FStar_TypeChecker_NBETerm.mkConstruct cfv [] []
             in
          let uu____2943 =
            FStar_List.map
              (fun uu____2958  ->
                 match uu____2958 with
                 | (p1,uu____2970) ->
                     let uu____2971 = translate_pat cfg p1  in
                     (uu____2971, FStar_Pervasives_Native.None)) pats
             in
          iapp cfg uu____2938 uu____2943
      | FStar_Syntax_Syntax.Pat_var bvar ->
          FStar_TypeChecker_NBETerm.mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_wild bvar ->
          FStar_TypeChecker_NBETerm.mkAccuVar bvar
      | FStar_Syntax_Syntax.Pat_dot_term (bvar,t) ->
          failwith "Pat_dot_term not implemented"

and (translate :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_NBETerm.t)
  =
  fun cfg  ->
    fun bs  ->
      fun e  ->
        let debug1 = debug cfg  in
        debug1
          (fun uu____3002  ->
             let uu____3003 =
               let uu____3004 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.tag_of_term uu____3004  in
             let uu____3005 =
               let uu____3006 = FStar_Syntax_Subst.compress e  in
               FStar_Syntax_Print.term_to_string uu____3006  in
             FStar_Util.print2 "Term: %s - %s\n" uu____3003 uu____3005);
        debug1
          (fun uu____3012  ->
             let uu____3013 =
               let uu____3014 =
                 FStar_List.map
                   (fun x  -> FStar_TypeChecker_NBETerm.t_to_string x) bs
                  in
               FStar_String.concat ";; " uu____3014  in
             FStar_Util.print1 "BS list: %s\n" uu____3013);
        (let uu____3019 =
           let uu____3020 = FStar_Syntax_Subst.compress e  in
           uu____3020.FStar_Syntax_Syntax.n  in
         match uu____3019 with
         | FStar_Syntax_Syntax.Tm_delayed (uu____3023,uu____3024) ->
             failwith "Tm_delayed: Impossible"
         | FStar_Syntax_Syntax.Tm_unknown  ->
             FStar_TypeChecker_NBETerm.Unknown
         | FStar_Syntax_Syntax.Tm_constant c ->
             let uu____3062 = translate_constant c  in
             FStar_TypeChecker_NBETerm.Constant uu____3062
         | FStar_Syntax_Syntax.Tm_bvar db ->
             FStar_List.nth bs db.FStar_Syntax_Syntax.index
         | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
             (debug1
                (fun uu____3077  ->
                   let uu____3078 = FStar_Syntax_Print.term_to_string t  in
                   let uu____3079 =
                     let uu____3080 =
                       FStar_List.map FStar_Syntax_Print.univ_to_string us
                        in
                     FStar_All.pipe_right uu____3080
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n"
                     uu____3078 uu____3079);
              (let uu____3085 = translate cfg bs t  in
               let uu____3086 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3090 = translate_univ bs x  in
                      FStar_TypeChecker_NBETerm.as_arg uu____3090) us
                  in
               iapp cfg uu____3085 uu____3086))
         | FStar_Syntax_Syntax.Tm_type u ->
             let uu____3092 =
               let uu____3093 = translate_univ bs u  in un_univ uu____3093
                in
             FStar_TypeChecker_NBETerm.Type_t uu____3092
         | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
             (debug_term e; failwith "Tm_arrow: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_refine (bv,tm) ->
             FStar_TypeChecker_NBETerm.Refinement
               (((fun y  -> translate cfg (y :: bs) tm)),
                 ((fun uu____3137  ->
                     let uu____3138 =
                       translate cfg bs bv.FStar_Syntax_Syntax.sort  in
                     FStar_TypeChecker_NBETerm.as_arg uu____3138)))
         | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3140,uu____3141) ->
             translate cfg bs t
         | FStar_Syntax_Syntax.Tm_uvar (uvar,t) ->
             (debug_term e; failwith "Tm_uvar: Not yet implemented")
         | FStar_Syntax_Syntax.Tm_name x ->
             FStar_TypeChecker_NBETerm.mkAccuVar x
         | FStar_Syntax_Syntax.Tm_abs ([],uu____3202,uu____3203) ->
             failwith "Impossible: abstraction with no binders"
         | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3228) ->
             let uu____3253 =
               let uu____3274 =
                 FStar_List.map
                   (fun x  ->
                      fun uu____3309  ->
                        let uu____3310 =
                          translate cfg bs
                            (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                           in
                        (uu____3310, (FStar_Pervasives_Native.snd x))) xs
                  in
               ((fun ys  -> translate cfg (FStar_List.rev_append ys bs) body),
                 uu____3274, (FStar_List.length xs))
                in
             FStar_TypeChecker_NBETerm.Lam uu____3253
         | FStar_Syntax_Syntax.Tm_fvar fvar1 -> translate_fv cfg bs fvar1
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3342;
                FStar_Syntax_Syntax.vars = uu____3343;_},arg::more::args)
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let uu____3403 = FStar_Syntax_Util.head_and_args e  in
             (match uu____3403 with
              | (reifyh,uu____3421) ->
                  let head1 =
                    FStar_Syntax_Syntax.mk_Tm_app reifyh [arg]
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  let uu____3465 =
                    FStar_Syntax_Syntax.mk_Tm_app head1 (more :: args)
                      FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                     in
                  translate cfg bs uu____3465)
         | FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                  (FStar_Const.Const_reify );
                FStar_Syntax_Syntax.pos = uu____3474;
                FStar_Syntax_Syntax.vars = uu____3475;_},arg::[])
             when
             (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
             ->
             let cfg1 =
               let uu___246_3517 = cfg  in
               {
                 FStar_TypeChecker_Cfg.steps =
                   (uu___246_3517.FStar_TypeChecker_Cfg.steps);
                 FStar_TypeChecker_Cfg.tcenv =
                   (uu___246_3517.FStar_TypeChecker_Cfg.tcenv);
                 FStar_TypeChecker_Cfg.debug =
                   (uu___246_3517.FStar_TypeChecker_Cfg.debug);
                 FStar_TypeChecker_Cfg.delta_level =
                   (uu___246_3517.FStar_TypeChecker_Cfg.delta_level);
                 FStar_TypeChecker_Cfg.primitive_steps =
                   (uu___246_3517.FStar_TypeChecker_Cfg.primitive_steps);
                 FStar_TypeChecker_Cfg.strong =
                   (uu___246_3517.FStar_TypeChecker_Cfg.strong);
                 FStar_TypeChecker_Cfg.memoize_lazy =
                   (uu___246_3517.FStar_TypeChecker_Cfg.memoize_lazy);
                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                   (uu___246_3517.FStar_TypeChecker_Cfg.normalize_pure_lets);
                 FStar_TypeChecker_Cfg.reifying = true
               }  in
             translate cfg1 bs (FStar_Pervasives_Native.fst arg)
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             (debug1
                (fun uu____3555  ->
                   let uu____3556 = FStar_Syntax_Print.term_to_string head1
                      in
                   let uu____3557 = FStar_Syntax_Print.args_to_string args
                      in
                   FStar_Util.print2 "Application: %s @ %s\n" uu____3556
                     uu____3557);
              (let uu____3558 = translate cfg bs head1  in
               let uu____3559 =
                 FStar_List.map
                   (fun x  ->
                      let uu____3581 =
                        translate cfg bs (FStar_Pervasives_Native.fst x)  in
                      (uu____3581, (FStar_Pervasives_Native.snd x))) args
                  in
               iapp cfg uu____3558 uu____3559))
         | FStar_Syntax_Syntax.Tm_match (scrut,branches) ->
             let rec case scrut1 =
               match scrut1 with
               | FStar_TypeChecker_NBETerm.Construct (c,us,args) ->
                   (debug1
                      (fun uu____3666  ->
                         let uu____3667 =
                           let uu____3668 =
                             FStar_All.pipe_right args
                               (FStar_List.map
                                  (fun uu____3691  ->
                                     match uu____3691 with
                                     | (x,q) ->
                                         let uu____3704 =
                                           FStar_TypeChecker_NBETerm.t_to_string
                                             x
                                            in
                                         Prims.strcat
                                           (if FStar_Util.is_some q
                                            then "#"
                                            else "") uu____3704))
                              in
                           FStar_All.pipe_right uu____3668
                             (FStar_String.concat "; ")
                            in
                         FStar_Util.print1 "Match args: %s\n" uu____3667);
                    (let uu____3708 = pickBranch cfg scrut1 branches  in
                     match uu____3708 with
                     | FStar_Pervasives_Native.Some (branch1,args1) ->
                         let uu____3729 =
                           FStar_List.fold_left
                             (fun bs1  -> fun x  -> x :: bs1) bs args1
                            in
                         translate cfg uu____3729 branch1
                     | FStar_Pervasives_Native.None  ->
                         FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                           make_branches))
               | FStar_TypeChecker_NBETerm.Constant c ->
                   let uu____3747 = pickBranch cfg scrut1 branches  in
                   (match uu____3747 with
                    | FStar_Pervasives_Native.Some (branch1,[]) ->
                        translate cfg bs branch1
                    | FStar_Pervasives_Native.Some (branch1,arg::[]) ->
                        translate cfg (arg :: bs) branch1
                    | FStar_Pervasives_Native.None  ->
                        FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                          make_branches
                    | FStar_Pervasives_Native.Some (uu____3781,hd1::tl1) ->
                        failwith
                          "Impossible: Matching on constants cannot bind more than one variable")
               | uu____3794 ->
                   FStar_TypeChecker_NBETerm.mkAccuMatch scrut1 case
                     make_branches
             
             and make_branches readback1 =
               let rec process_pattern bs1 p =
                 let uu____3827 =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_constant c ->
                       (bs1, (FStar_Syntax_Syntax.Pat_constant c))
                   | FStar_Syntax_Syntax.Pat_cons (fvar1,args) ->
                       let uu____3861 =
                         FStar_List.fold_left
                           (fun uu____3899  ->
                              fun uu____3900  ->
                                match (uu____3899, uu____3900) with
                                | ((bs2,args1),(arg,b)) ->
                                    let uu____3981 = process_pattern bs2 arg
                                       in
                                    (match uu____3981 with
                                     | (bs',arg') ->
                                         (bs', ((arg', b) :: args1))))
                           (bs1, []) args
                          in
                       (match uu____3861 with
                        | (bs',args') ->
                            (bs',
                              (FStar_Syntax_Syntax.Pat_cons
                                 (fvar1, (FStar_List.rev args')))))
                   | FStar_Syntax_Syntax.Pat_var bvar ->
                       let x =
                         let uu____4070 =
                           let uu____4071 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4071  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4070
                          in
                       let uu____4072 =
                         let uu____4075 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4075 :: bs1  in
                       (uu____4072, (FStar_Syntax_Syntax.Pat_var x))
                   | FStar_Syntax_Syntax.Pat_wild bvar ->
                       let x =
                         let uu____4080 =
                           let uu____4081 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4081  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4080
                          in
                       let uu____4082 =
                         let uu____4085 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4085 :: bs1  in
                       (uu____4082, (FStar_Syntax_Syntax.Pat_wild x))
                   | FStar_Syntax_Syntax.Pat_dot_term (bvar,tm) ->
                       let x =
                         let uu____4095 =
                           let uu____4096 =
                             translate cfg bs1 bvar.FStar_Syntax_Syntax.sort
                              in
                           readback1 uu____4096  in
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None uu____4095
                          in
                       let uu____4097 =
                         let uu____4100 =
                           FStar_TypeChecker_NBETerm.mkAccuVar x  in
                         uu____4100 :: bs1  in
                       let uu____4101 =
                         let uu____4102 =
                           let uu____4109 =
                             let uu____4112 = translate cfg bs1 tm  in
                             readback1 uu____4112  in
                           (x, uu____4109)  in
                         FStar_Syntax_Syntax.Pat_dot_term uu____4102  in
                       (uu____4097, uu____4101)
                    in
                 match uu____3827 with
                 | (bs2,p_new) ->
                     (bs2,
                       (let uu___247_4132 = p  in
                        {
                          FStar_Syntax_Syntax.v = p_new;
                          FStar_Syntax_Syntax.p =
                            (uu___247_4132.FStar_Syntax_Syntax.p)
                        }))
                  in
               FStar_List.map
                 (fun uu____4151  ->
                    match uu____4151 with
                    | (pat,when_clause,e1) ->
                        let uu____4173 = process_pattern bs pat  in
                        (match uu____4173 with
                         | (bs',pat') ->
                             let uu____4186 =
                               let uu____4187 =
                                 let uu____4190 = translate cfg bs' e1  in
                                 readback1 uu____4190  in
                               (pat', when_clause, uu____4187)  in
                             FStar_Syntax_Util.branch uu____4186)) branches
              in let uu____4199 = translate cfg bs scrut  in case uu____4199
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic (m,t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic (m, t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_meta
             (e1,FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t)) when
             cfg.FStar_TypeChecker_Cfg.reifying ->
             translate_monadic_lift (m, m', t) cfg bs e1
         | FStar_Syntax_Syntax.Tm_let ((false ,lbs),body) ->
             let bs' =
               FStar_List.fold_left
                 (fun bs'  ->
                    fun lb  ->
                      let b = translate_letbinding cfg bs lb  in b :: bs') bs
                 lbs
                in
             translate cfg bs' body
         | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) ->
             let uu____4272 = make_rec_env lbs bs  in
             translate cfg uu____4272 body
         | FStar_Syntax_Syntax.Tm_meta (e1,uu____4276) -> translate cfg bs e1
         | FStar_Syntax_Syntax.Tm_quoted (uu____4281,uu____4282) ->
             let uu____4287 =
               let uu____4288 =
                 let uu____4289 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4289  in
               Prims.strcat "Not yet handled: " uu____4288  in
             failwith uu____4287
         | FStar_Syntax_Syntax.Tm_lazy uu____4290 ->
             let uu____4291 =
               let uu____4292 =
                 let uu____4293 = FStar_Syntax_Subst.compress e  in
                 FStar_Syntax_Print.tag_of_term uu____4293  in
               Prims.strcat "Not yet handled: " uu____4292  in
             failwith uu____4291)

and (translate_monadic :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                    FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4294  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4294 with
          | (m,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              (match e1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                   let uu____4329 =
                     let uu____4338 =
                       FStar_TypeChecker_Env.norm_eff_name
                         cfg.FStar_TypeChecker_Cfg.tcenv m
                        in
                     FStar_TypeChecker_Env.effect_decl_opt
                       cfg.FStar_TypeChecker_Cfg.tcenv uu____4338
                      in
                   (match uu____4329 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4345 =
                          let uu____4346 = FStar_Ident.string_of_lid m  in
                          FStar_Util.format1
                            "Effect declaration not found: %s" uu____4346
                           in
                        failwith uu____4345
                    | FStar_Pervasives_Native.Some (ed,q) ->
                        let cfg' =
                          let uu___248_4360 = cfg  in
                          {
                            FStar_TypeChecker_Cfg.steps =
                              (uu___248_4360.FStar_TypeChecker_Cfg.steps);
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___248_4360.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___248_4360.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level =
                              (uu___248_4360.FStar_TypeChecker_Cfg.delta_level);
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___248_4360.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___248_4360.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___248_4360.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets =
                              (uu___248_4360.FStar_TypeChecker_Cfg.normalize_pure_lets);
                            FStar_TypeChecker_Cfg.reifying = false
                          }  in
                        let body_lam =
                          let body_rc =
                            {
                              FStar_Syntax_Syntax.residual_effect = m;
                              FStar_Syntax_Syntax.residual_typ =
                                (FStar_Pervasives_Native.Some ty);
                              FStar_Syntax_Syntax.residual_flags = []
                            }  in
                          let uu____4367 =
                            let uu____4374 =
                              let uu____4375 =
                                let uu____4394 =
                                  let uu____4403 =
                                    let uu____4410 =
                                      FStar_Util.left
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    (uu____4410,
                                      FStar_Pervasives_Native.None)
                                     in
                                  [uu____4403]  in
                                (uu____4394, body,
                                  (FStar_Pervasives_Native.Some body_rc))
                                 in
                              FStar_Syntax_Syntax.Tm_abs uu____4375  in
                            FStar_Syntax_Syntax.mk uu____4374  in
                          uu____4367 FStar_Pervasives_Native.None
                            body.FStar_Syntax_Syntax.pos
                           in
                        let maybe_range_arg =
                          let uu____4447 =
                            FStar_Util.for_some
                              (FStar_Syntax_Util.attr_eq
                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                              ed.FStar_Syntax_Syntax.eff_attrs
                             in
                          if uu____4447
                          then
                            let uu____4454 =
                              let uu____4459 =
                                let uu____4460 =
                                  FStar_Syntax_Embeddings.embed
                                    FStar_Syntax_Embeddings.e_range
                                    lb.FStar_Syntax_Syntax.lbpos
                                    lb.FStar_Syntax_Syntax.lbpos
                                   in
                                translate cfg [] uu____4460  in
                              (uu____4459, FStar_Pervasives_Native.None)  in
                            let uu____4461 =
                              let uu____4468 =
                                let uu____4473 =
                                  let uu____4474 =
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_range
                                      body.FStar_Syntax_Syntax.pos
                                      body.FStar_Syntax_Syntax.pos
                                     in
                                  translate cfg [] uu____4474  in
                                (uu____4473, FStar_Pervasives_Native.None)
                                 in
                              [uu____4468]  in
                            uu____4454 :: uu____4461
                          else []  in
                        let uu____4492 =
                          let uu____4493 =
                            let uu____4494 =
                              FStar_Syntax_Util.un_uinst
                                (FStar_Pervasives_Native.snd
                                   ed.FStar_Syntax_Syntax.bind_repr)
                               in
                            translate cfg' [] uu____4494  in
                          iapp cfg uu____4493
                            [((FStar_TypeChecker_NBETerm.Univ
                                 FStar_Syntax_Syntax.U_unknown),
                               FStar_Pervasives_Native.None);
                            ((FStar_TypeChecker_NBETerm.Univ
                                FStar_Syntax_Syntax.U_unknown),
                              FStar_Pervasives_Native.None)]
                           in
                        let uu____4511 =
                          let uu____4512 =
                            let uu____4519 =
                              let uu____4524 =
                                translate cfg' bs
                                  lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              (uu____4524, FStar_Pervasives_Native.None)  in
                            let uu____4525 =
                              let uu____4532 =
                                let uu____4537 = translate cfg' bs ty  in
                                (uu____4537, FStar_Pervasives_Native.None)
                                 in
                              [uu____4532]  in
                            uu____4519 :: uu____4525  in
                          let uu____4550 =
                            let uu____4557 =
                              let uu____4564 =
                                let uu____4571 =
                                  let uu____4576 =
                                    translate cfg bs
                                      lb.FStar_Syntax_Syntax.lbdef
                                     in
                                  (uu____4576, FStar_Pervasives_Native.None)
                                   in
                                let uu____4577 =
                                  let uu____4584 =
                                    let uu____4591 =
                                      let uu____4596 =
                                        translate cfg bs body_lam  in
                                      (uu____4596,
                                        FStar_Pervasives_Native.None)
                                       in
                                    [uu____4591]  in
                                  (FStar_TypeChecker_NBETerm.Unknown,
                                    FStar_Pervasives_Native.None) ::
                                    uu____4584
                                   in
                                uu____4571 :: uu____4577  in
                              (FStar_TypeChecker_NBETerm.Unknown,
                                FStar_Pervasives_Native.None) :: uu____4564
                               in
                            FStar_List.append maybe_range_arg uu____4557  in
                          FStar_List.append uu____4512 uu____4550  in
                        iapp cfg uu____4492 uu____4511)
               | FStar_Syntax_Syntax.Tm_app
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reflect uu____4625);
                      FStar_Syntax_Syntax.pos = uu____4626;
                      FStar_Syntax_Syntax.vars = uu____4627;_},(e2,uu____4629)::[])
                   ->
                   translate
                     (let uu___249_4670 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (uu___249_4670.FStar_TypeChecker_Cfg.steps);
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___249_4670.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___249_4670.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___249_4670.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___249_4670.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___249_4670.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___249_4670.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___249_4670.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying = false
                      }) bs e2
               | FStar_Syntax_Syntax.Tm_app uu____4671 -> translate cfg bs e1
               | uu____4688 ->
                   let uu____4689 =
                     let uu____4690 = FStar_Syntax_Print.tag_of_term e1  in
                     FStar_Util.format1
                       "Unexpected case in translate_monadic: %s" uu____4690
                      in
                   failwith uu____4689)

and (translate_monadic_lift :
  (FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.monad_name,FStar_Syntax_Syntax.term'
                                                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 ->
    FStar_TypeChecker_Cfg.cfg ->
      FStar_TypeChecker_NBETerm.t Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_TypeChecker_NBETerm.t)
  =
  fun uu____4691  ->
    fun cfg  ->
      fun bs  ->
        fun e  ->
          match uu____4691 with
          | (msrc,mtgt,ty) ->
              let e1 = FStar_Syntax_Util.unascribe e  in
              let uu____4715 =
                (FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc)
                 in
              if uu____4715
              then
                let ed =
                  let uu____4717 =
                    FStar_TypeChecker_Env.norm_eff_name
                      cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                     in
                  FStar_TypeChecker_Env.get_effect_decl
                    cfg.FStar_TypeChecker_Cfg.tcenv uu____4717
                   in
                let cfg' =
                  let uu___250_4719 = cfg  in
                  {
                    FStar_TypeChecker_Cfg.steps =
                      (uu___250_4719.FStar_TypeChecker_Cfg.steps);
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___250_4719.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___250_4719.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      (uu___250_4719.FStar_TypeChecker_Cfg.delta_level);
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___250_4719.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___250_4719.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___250_4719.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___250_4719.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying = false
                  }  in
                let uu____4720 =
                  let uu____4721 =
                    let uu____4722 =
                      FStar_Syntax_Util.un_uinst
                        (FStar_Pervasives_Native.snd
                           ed.FStar_Syntax_Syntax.return_repr)
                       in
                    translate cfg' [] uu____4722  in
                  iapp cfg uu____4721
                    [((FStar_TypeChecker_NBETerm.Univ
                         FStar_Syntax_Syntax.U_unknown),
                       FStar_Pervasives_Native.None)]
                   in
                let uu____4735 =
                  let uu____4736 =
                    let uu____4741 = translate cfg' bs ty  in
                    (uu____4741, FStar_Pervasives_Native.None)  in
                  let uu____4742 =
                    let uu____4749 =
                      let uu____4754 = translate cfg' bs e1  in
                      (uu____4754, FStar_Pervasives_Native.None)  in
                    [uu____4749]  in
                  uu____4736 :: uu____4742  in
                iapp cfg uu____4720 uu____4735
              else
                (let uu____4768 =
                   FStar_TypeChecker_Env.monad_leq
                     cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt
                    in
                 match uu____4768 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4771 =
                       let uu____4772 = FStar_Ident.text_of_lid msrc  in
                       let uu____4773 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                         uu____4772 uu____4773
                        in
                     failwith uu____4771
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4774;
                       FStar_TypeChecker_Env.mtarget = uu____4775;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4776;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.None ;_};_}
                     ->
                     let uu____4798 =
                       let uu____4799 = FStar_Ident.text_of_lid msrc  in
                       let uu____4800 = FStar_Ident.text_of_lid mtgt  in
                       FStar_Util.format2
                         "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                         uu____4799 uu____4800
                        in
                     failwith uu____4798
                 | FStar_Pervasives_Native.Some
                     { FStar_TypeChecker_Env.msource = uu____4801;
                       FStar_TypeChecker_Env.mtarget = uu____4802;
                       FStar_TypeChecker_Env.mlift =
                         { FStar_TypeChecker_Env.mlift_wp = uu____4803;
                           FStar_TypeChecker_Env.mlift_term =
                             FStar_Pervasives_Native.Some lift;_};_}
                     ->
                     let lift_lam =
                       let x =
                         FStar_Syntax_Syntax.new_bv
                           FStar_Pervasives_Native.None
                           FStar_Syntax_Syntax.tun
                          in
                       let uu____4842 =
                         let uu____4845 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         lift FStar_Syntax_Syntax.U_unknown ty
                           FStar_Syntax_Syntax.tun uu____4845
                          in
                       FStar_Syntax_Util.abs
                         [(x, FStar_Pervasives_Native.None)] uu____4842
                         FStar_Pervasives_Native.None
                        in
                     let cfg' =
                       let uu___251_4861 = cfg  in
                       {
                         FStar_TypeChecker_Cfg.steps =
                           (uu___251_4861.FStar_TypeChecker_Cfg.steps);
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___251_4861.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___251_4861.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level =
                           (uu___251_4861.FStar_TypeChecker_Cfg.delta_level);
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___251_4861.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___251_4861.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___251_4861.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets =
                           (uu___251_4861.FStar_TypeChecker_Cfg.normalize_pure_lets);
                         FStar_TypeChecker_Cfg.reifying = false
                       }  in
                     let uu____4862 = translate cfg' [] lift_lam  in
                     let uu____4863 =
                       let uu____4864 =
                         let uu____4869 = translate cfg bs e1  in
                         (uu____4869, FStar_Pervasives_Native.None)  in
                       [uu____4864]  in
                     iapp cfg uu____4862 uu____4863)

and (readback :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_NBETerm.t -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun x  ->
      let debug1 = debug cfg  in
      debug1
        (fun uu____4893  ->
           let uu____4894 = FStar_TypeChecker_NBETerm.t_to_string x  in
           FStar_Util.print1 "Readback: %s\n" uu____4894);
      (match x with
       | FStar_TypeChecker_NBETerm.Univ u ->
           failwith "Readback of universes should not occur"
       | FStar_TypeChecker_NBETerm.Unknown  ->
           FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit )
           -> FStar_Syntax_Syntax.unit_const
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (true )) -> FStar_Syntax_Util.exp_true_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool
           (false )) -> FStar_Syntax_Util.exp_false_bool
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int i)
           ->
           let uu____4897 = FStar_BigInt.string_of_big_int i  in
           FStar_All.pipe_right uu____4897 FStar_Syntax_Util.exp_int
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String
           (s,r)) ->
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, r)))
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char
           c) -> FStar_Syntax_Util.exp_char c
       | FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range
           r) ->
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range r
             FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Type_t u ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
       | FStar_TypeChecker_NBETerm.Lam (f,targs,arity) ->
           let uu____4935 =
             FStar_List.fold_left
               (fun uu____4976  ->
                  fun tf  ->
                    match uu____4976 with
                    | (args,accus) ->
                        let uu____5026 = tf ()  in
                        (match uu____5026 with
                         | (xt,q) ->
                             let x1 =
                               let uu____5046 = readback cfg xt  in
                               FStar_Syntax_Syntax.new_bv
                                 FStar_Pervasives_Native.None uu____5046
                                in
                             let uu____5047 =
                               let uu____5050 =
                                 FStar_TypeChecker_NBETerm.mkAccuVar x1  in
                               uu____5050 :: accus  in
                             (((x1, q) :: args), uu____5047))) ([], []) targs
              in
           (match uu____4935 with
            | (args,accus) ->
                let body =
                  let uu____5094 = f accus  in readback cfg uu____5094  in
                FStar_Syntax_Util.abs args body FStar_Pervasives_Native.None)
       | FStar_TypeChecker_NBETerm.Refinement (f,targ) ->
           let x1 =
             let uu____5118 =
               let uu____5119 =
                 let uu____5120 = targ ()  in
                 FStar_Pervasives_Native.fst uu____5120  in
               readback cfg uu____5119  in
             FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
               uu____5118
              in
           let body =
             let uu____5126 =
               let uu____5127 = FStar_TypeChecker_NBETerm.mkAccuVar x1  in
               f uu____5127  in
             readback cfg uu____5126  in
           FStar_Syntax_Util.refine x1 body
       | FStar_TypeChecker_NBETerm.Construct (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5166  ->
                  match uu____5166 with
                  | (x1,q) ->
                      let uu____5177 = readback cfg x1  in (uu____5177, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5196 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5203::uu____5204 ->
                let uu____5207 =
                  let uu____5210 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5210
                    (FStar_List.rev us)
                   in
                apply uu____5207
            | [] ->
                let uu____5211 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5211)
       | FStar_TypeChecker_NBETerm.FV (fv,us,args) ->
           let args1 =
             map_rev
               (fun uu____5252  ->
                  match uu____5252 with
                  | (x1,q) ->
                      let uu____5263 = readback cfg x1  in (uu____5263, q))
               args
              in
           let apply tm =
             match args1 with
             | [] -> tm
             | uu____5282 -> FStar_Syntax_Util.mk_app tm args1  in
           (match us with
            | uu____5289::uu____5290 ->
                let uu____5293 =
                  let uu____5296 =
                    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst uu____5296
                    (FStar_List.rev us)
                   in
                apply uu____5293
            | [] ->
                let uu____5297 =
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                apply uu____5297)
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,[])
           -> FStar_Syntax_Syntax.bv_to_name bv
       | FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var bv,ts)
           ->
           let args =
             map_rev
               (fun uu____5344  ->
                  match uu____5344 with
                  | (x1,q) ->
                      let uu____5355 = readback cfg x1  in (uu____5355, q))
               ts
              in
           let uu____5356 = FStar_Syntax_Syntax.bv_to_name bv  in
           FStar_Syntax_Util.mk_app uu____5356 args
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Match (scrut,cases,make_branches),ts)
           ->
           let args =
             map_rev
               (fun uu____5416  ->
                  match uu____5416 with
                  | (x1,q) ->
                      let uu____5427 = readback cfg x1  in (uu____5427, q))
               ts
              in
           let head1 =
             let scrut_new = readback cfg scrut  in
             let branches_new = make_branches (readback cfg)  in
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_match (scrut_new, branches_new))
               FStar_Pervasives_Native.None FStar_Range.dummyRange
              in
           (match ts with
            | [] -> head1
            | uu____5457 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Accu
           (FStar_TypeChecker_NBETerm.Rec (lb,lbs,bs),ts) ->
           let rec curry hd1 args =
             match args with
             | [] -> hd1
             | arg::[] ->
                 app cfg hd1 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
             | arg::args1 ->
                 let uu____5544 = curry hd1 args1  in
                 app cfg uu____5544 (FStar_Pervasives_Native.fst arg)
                   (FStar_Pervasives_Native.snd arg)
              in
           let args_no = count_abstractions lb.FStar_Syntax_Syntax.lbdef  in
           let uu____5546 = test_args ts args_no  in
           if uu____5546
           then
             let uu____5547 =
               let uu____5548 =
                 let uu____5549 = make_rec_env lbs bs  in
                 translate_letbinding cfg uu____5549 lb  in
               curry uu____5548 ts  in
             readback cfg uu____5547
           else
             (let head1 =
                let f =
                  match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inl bv -> FStar_Syntax_Syntax.bv_to_name bv
                  | FStar_Util.Inr fv -> failwith "Not yet implemented"  in
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_let ((true, lbs), f))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              let args =
                map_rev
                  (fun uu____5594  ->
                     match uu____5594 with
                     | (x1,q) ->
                         let uu____5605 = readback cfg x1  in (uu____5605, q))
                  ts
                 in
              match ts with
              | [] -> head1
              | uu____5610 -> FStar_Syntax_Util.mk_app head1 args)
       | FStar_TypeChecker_NBETerm.Arrow uu____5617 ->
           failwith "Arrows not yet handled")

type step =
  | Primops 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | Reify 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____5658 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____5665 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____5681 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____5701 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____5714 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____5720 -> false
  
let (step_as_normalizer_step : step -> FStar_TypeChecker_Env.step) =
  fun uu___245_5725  ->
    match uu___245_5725 with
    | Primops  -> FStar_TypeChecker_Env.Primops
    | UnfoldUntil d -> FStar_TypeChecker_Env.UnfoldUntil d
    | UnfoldOnly lids -> FStar_TypeChecker_Env.UnfoldOnly lids
    | UnfoldAttr attr -> FStar_TypeChecker_Env.UnfoldAttr attr
    | UnfoldTac  -> FStar_TypeChecker_Env.UnfoldTac
    | Reify  -> FStar_TypeChecker_Env.Reify
  
let (normalize' :
  FStar_TypeChecker_Env.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg = FStar_TypeChecker_Cfg.config steps env  in
        let cfg1 =
          let uu___252_5752 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___253_5755 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___253_5755.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___253_5755.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___253_5755.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___253_5755.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___253_5755.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___253_5755.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___253_5755.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___253_5755.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___253_5755.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___253_5755.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___253_5755.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___253_5755.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___253_5755.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___253_5755.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___253_5755.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___253_5755.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___253_5755.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___253_5755.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___252_5752.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___252_5752.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___252_5752.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___252_5752.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___252_5752.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___252_5752.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___252_5752.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___252_5752.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____5759  ->
             let uu____5760 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____5760);
        (let uu____5761 = translate cfg1 [] e  in readback cfg1 uu____5761)
  
let (test_normalize :
  step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun e  ->
        let cfg =
          let uu____5782 = FStar_List.map step_as_normalizer_step steps  in
          FStar_TypeChecker_Cfg.config uu____5782 env  in
        let cfg1 =
          let uu___254_5786 = cfg  in
          {
            FStar_TypeChecker_Cfg.steps =
              (let uu___255_5789 = cfg.FStar_TypeChecker_Cfg.steps  in
               {
                 FStar_TypeChecker_Cfg.beta =
                   (uu___255_5789.FStar_TypeChecker_Cfg.beta);
                 FStar_TypeChecker_Cfg.iota =
                   (uu___255_5789.FStar_TypeChecker_Cfg.iota);
                 FStar_TypeChecker_Cfg.zeta =
                   (uu___255_5789.FStar_TypeChecker_Cfg.zeta);
                 FStar_TypeChecker_Cfg.weak =
                   (uu___255_5789.FStar_TypeChecker_Cfg.weak);
                 FStar_TypeChecker_Cfg.hnf =
                   (uu___255_5789.FStar_TypeChecker_Cfg.hnf);
                 FStar_TypeChecker_Cfg.primops =
                   (uu___255_5789.FStar_TypeChecker_Cfg.primops);
                 FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                   (uu___255_5789.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                 FStar_TypeChecker_Cfg.unfold_until =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unfold_until);
                 FStar_TypeChecker_Cfg.unfold_only =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unfold_only);
                 FStar_TypeChecker_Cfg.unfold_fully =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unfold_fully);
                 FStar_TypeChecker_Cfg.unfold_attr =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unfold_attr);
                 FStar_TypeChecker_Cfg.unfold_tac =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unfold_tac);
                 FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                   (uu___255_5789.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                 FStar_TypeChecker_Cfg.simplify =
                   (uu___255_5789.FStar_TypeChecker_Cfg.simplify);
                 FStar_TypeChecker_Cfg.erase_universes =
                   (uu___255_5789.FStar_TypeChecker_Cfg.erase_universes);
                 FStar_TypeChecker_Cfg.allow_unbound_universes =
                   (uu___255_5789.FStar_TypeChecker_Cfg.allow_unbound_universes);
                 FStar_TypeChecker_Cfg.reify_ = true;
                 FStar_TypeChecker_Cfg.compress_uvars =
                   (uu___255_5789.FStar_TypeChecker_Cfg.compress_uvars);
                 FStar_TypeChecker_Cfg.no_full_norm =
                   (uu___255_5789.FStar_TypeChecker_Cfg.no_full_norm);
                 FStar_TypeChecker_Cfg.check_no_uvars =
                   (uu___255_5789.FStar_TypeChecker_Cfg.check_no_uvars);
                 FStar_TypeChecker_Cfg.unmeta =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unmeta);
                 FStar_TypeChecker_Cfg.unascribe =
                   (uu___255_5789.FStar_TypeChecker_Cfg.unascribe);
                 FStar_TypeChecker_Cfg.in_full_norm_request =
                   (uu___255_5789.FStar_TypeChecker_Cfg.in_full_norm_request);
                 FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                   (uu___255_5789.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                 FStar_TypeChecker_Cfg.nbe_step =
                   (uu___255_5789.FStar_TypeChecker_Cfg.nbe_step)
               });
            FStar_TypeChecker_Cfg.tcenv =
              (uu___254_5786.FStar_TypeChecker_Cfg.tcenv);
            FStar_TypeChecker_Cfg.debug =
              (uu___254_5786.FStar_TypeChecker_Cfg.debug);
            FStar_TypeChecker_Cfg.delta_level =
              (uu___254_5786.FStar_TypeChecker_Cfg.delta_level);
            FStar_TypeChecker_Cfg.primitive_steps =
              (uu___254_5786.FStar_TypeChecker_Cfg.primitive_steps);
            FStar_TypeChecker_Cfg.strong =
              (uu___254_5786.FStar_TypeChecker_Cfg.strong);
            FStar_TypeChecker_Cfg.memoize_lazy =
              (uu___254_5786.FStar_TypeChecker_Cfg.memoize_lazy);
            FStar_TypeChecker_Cfg.normalize_pure_lets =
              (uu___254_5786.FStar_TypeChecker_Cfg.normalize_pure_lets);
            FStar_TypeChecker_Cfg.reifying =
              (uu___254_5786.FStar_TypeChecker_Cfg.reifying)
          }  in
        debug cfg1
          (fun uu____5793  ->
             let uu____5794 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.print1 "Calling NBE with %s" uu____5794);
        (let r =
           let uu____5796 = translate cfg1 [] e  in readback cfg1 uu____5796
            in
         debug cfg1
           (fun uu____5800  ->
              let uu____5801 = FStar_Syntax_Print.term_to_string r  in
              FStar_Util.print1 "NBE returned %s" uu____5801);
         r)
  