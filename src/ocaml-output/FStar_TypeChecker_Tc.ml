open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____12 l in
          let uu___61_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___61_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___61_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___61_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___61_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___61_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___61_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___61_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___61_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___61_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___61_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___61_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___61_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___61_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___61_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___61_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___61_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___61_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___61_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___61_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___61_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___61_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___61_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___61_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___61_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___61_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___61_13.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___61_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___61_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___61_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___61_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___61_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___61_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___61_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___61_13.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l in
          let uu___62_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___62_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___62_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___62_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___62_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___62_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___62_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___62_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___62_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___62_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___62_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___62_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___62_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___62_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___62_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___62_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___62_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___62_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___62_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___62_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___62_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___62_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___62_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___62_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___62_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___62_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___62_29.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___62_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___62_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___62_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___62_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___62_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___62_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___62_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___62_29.FStar_TypeChecker_Env.dep_graph)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____38 =
         let uu____39 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39 in
       Prims.op_Negation uu____38)
let get_tactic_fv:
  'Auu____44 .
    'Auu____44 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____60) ->
            let uu____65 =
              let uu____66 = FStar_Syntax_Subst.compress h' in
              uu____66.FStar_Syntax_Syntax.n in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____72 -> FStar_Pervasives_Native.None)
        | uu____73 -> FStar_Pervasives_Native.None
let is_builtin_tactic: FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____80 =
        let uu____83 = FStar_List.splitAt (Prims.parse_int "2") path in
        FStar_Pervasives_Native.fst uu____83 in
      match uu____80 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____96 -> false
    else false
let user_tactics_modules: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____141 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____141 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____162 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____162
         then
           let uu____163 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____163
         else ());
        (let uu____165 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____165 with
         | (t',uu____173,uu____174) ->
             ((let uu____176 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____176
               then
                 let uu____177 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____177
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____188 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____188
let check_nogen:
  'Auu____193 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____193 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____213 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____213)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____240 =
          let uu____241 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          FStar_Errors.raise_error uu____241 (FStar_Ident.range_of_lid m) in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____285)::(wp,uu____287)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____302 -> fail ())
        | uu____303 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____310 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____310 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____336 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____336 t in
          let open_univs_binders n_binders bs =
            let uu____346 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____346 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____354 =
            let uu____361 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders in
            let uu____362 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____361 uu____362 in
          (match uu____354 with
           | (effect_params_un,signature_un,opening) ->
               let uu____372 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
               (match uu____372 with
                | (effect_params,env,uu____381) ->
                    let uu____382 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un in
                    (match uu____382 with
                     | (signature,uu____388) ->
                         let ed1 =
                           let uu___63_390 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___63_390.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___63_390.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___63_390.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___63_390.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___63_390.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___63_390.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___63_390.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___63_390.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___63_390.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___63_390.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___63_390.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___63_390.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___63_390.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___63_390.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___63_390.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___63_390.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___63_390.FStar_Syntax_Syntax.actions)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____406 ->
                               let op uu____428 =
                                 match uu____428 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____448 =
                                       let uu____449 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____458 =
                                         open_univs (n_effect_params + n_us)
                                           t in
                                       FStar_Syntax_Subst.subst uu____449
                                         uu____458 in
                                     (us, uu____448) in
                               let uu___64_471 = ed1 in
                               let uu____472 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____473 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____474 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____475 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____476 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____477 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____478 =
                                 op ed1.FStar_Syntax_Syntax.assert_p in
                               let uu____479 =
                                 op ed1.FStar_Syntax_Syntax.assume_p in
                               let uu____480 =
                                 op ed1.FStar_Syntax_Syntax.null_wp in
                               let uu____481 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____482 =
                                 let uu____483 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____483 in
                               let uu____494 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____495 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____496 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___65_504 = a in
                                      let uu____505 =
                                        let uu____506 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____506 in
                                      let uu____517 =
                                        let uu____518 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd uu____518 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___65_504.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___65_504.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___65_504.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___65_504.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____505;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____517
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___64_471.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___64_471.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___64_471.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___64_471.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____472;
                                 FStar_Syntax_Syntax.bind_wp = uu____473;
                                 FStar_Syntax_Syntax.if_then_else = uu____474;
                                 FStar_Syntax_Syntax.ite_wp = uu____475;
                                 FStar_Syntax_Syntax.stronger = uu____476;
                                 FStar_Syntax_Syntax.close_wp = uu____477;
                                 FStar_Syntax_Syntax.assert_p = uu____478;
                                 FStar_Syntax_Syntax.assume_p = uu____479;
                                 FStar_Syntax_Syntax.null_wp = uu____480;
                                 FStar_Syntax_Syntax.trivial = uu____481;
                                 FStar_Syntax_Syntax.repr = uu____482;
                                 FStar_Syntax_Syntax.return_repr = uu____494;
                                 FStar_Syntax_Syntax.bind_repr = uu____495;
                                 FStar_Syntax_Syntax.actions = uu____496
                               } in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____555 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t in
                             FStar_Errors.raise_error uu____555
                               (FStar_Ident.range_of_lid mname) in
                           let uu____566 =
                             let uu____567 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____567.FStar_Syntax_Syntax.n in
                           match uu____566 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a,uu____602)::(wp,uu____604)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____619 -> fail signature1)
                           | uu____620 -> fail signature1 in
                         let uu____621 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____621 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____643 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____650 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un in
                                    (match uu____650 with
                                     | (signature1,uu____662) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____663 ->
                                    let uu____666 =
                                      let uu____671 =
                                        let uu____672 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____672) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____671 in
                                    (match uu____666 with
                                     | (uu____681,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env1 =
                                let uu____684 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env uu____684 in
                              ((let uu____686 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____686
                                then
                                  let uu____687 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____688 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____689 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____690 =
                                    let uu____691 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____691 in
                                  let uu____692 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____687 uu____688 uu____689 uu____690
                                    uu____692
                                else ());
                               (let check_and_gen' env2 uu____708 k =
                                  match uu____708 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____722::uu____723 ->
                                           let uu____726 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____726 with
                                            | (us1,t1) ->
                                                let uu____735 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____735 with
                                                 | (us2,t2) ->
                                                     let uu____742 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k in
                                                     let uu____743 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____743)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____748 =
                                      let uu____755 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____756 =
                                        let uu____759 =
                                          let uu____760 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____760 in
                                        [uu____759] in
                                      uu____755 :: uu____756 in
                                    let uu____761 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____748
                                      uu____761 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____765 = fresh_effect_signature () in
                                  match uu____765 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____781 =
                                          let uu____788 =
                                            let uu____789 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____789 in
                                          [uu____788] in
                                        let uu____790 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____781
                                          uu____790 in
                                      let expected_k =
                                        let uu____796 =
                                          let uu____803 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____804 =
                                            let uu____807 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____808 =
                                              let uu____811 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____812 =
                                                let uu____815 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____816 =
                                                  let uu____819 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____819] in
                                                uu____815 :: uu____816 in
                                              uu____811 :: uu____812 in
                                            uu____807 :: uu____808 in
                                          uu____803 :: uu____804 in
                                        let uu____820 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____796
                                          uu____820 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____825 =
                                      let uu____826 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____826
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____825 in
                                  let expected_k =
                                    let uu____838 =
                                      let uu____845 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____846 =
                                        let uu____849 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____850 =
                                          let uu____853 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____854 =
                                            let uu____857 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____857] in
                                          uu____853 :: uu____854 in
                                        uu____849 :: uu____850 in
                                      uu____845 :: uu____846 in
                                    let uu____858 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____838
                                      uu____858 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____865 =
                                      let uu____872 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____873 =
                                        let uu____876 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____876] in
                                      uu____872 :: uu____873 in
                                    let uu____877 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____865
                                      uu____877 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____881 = FStar_Syntax_Util.type_u () in
                                  match uu____881 with
                                  | (t,uu____887) ->
                                      let expected_k =
                                        let uu____891 =
                                          let uu____898 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____899 =
                                            let uu____902 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____903 =
                                              let uu____906 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____906] in
                                            uu____902 :: uu____903 in
                                          uu____898 :: uu____899 in
                                        let uu____907 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____891
                                          uu____907 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____912 =
                                      let uu____913 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____913
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____912 in
                                  let b_wp_a =
                                    let uu____925 =
                                      let uu____932 =
                                        let uu____933 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____933 in
                                      [uu____932] in
                                    let uu____934 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____925
                                      uu____934 in
                                  let expected_k =
                                    let uu____940 =
                                      let uu____947 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____948 =
                                        let uu____951 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____952 =
                                          let uu____955 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____955] in
                                        uu____951 :: uu____952 in
                                      uu____947 :: uu____948 in
                                    let uu____956 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____940
                                      uu____956 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let assert_p =
                                  let expected_k =
                                    let uu____963 =
                                      let uu____970 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____971 =
                                        let uu____974 =
                                          let uu____975 =
                                            let uu____976 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____976
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____975 in
                                        let uu____985 =
                                          let uu____988 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____988] in
                                        uu____974 :: uu____985 in
                                      uu____970 :: uu____971 in
                                    let uu____989 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____963
                                      uu____989 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k in
                                let assume_p =
                                  let expected_k =
                                    let uu____996 =
                                      let uu____1003 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1004 =
                                        let uu____1007 =
                                          let uu____1008 =
                                            let uu____1009 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____1009
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1008 in
                                        let uu____1018 =
                                          let uu____1021 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1021] in
                                        uu____1007 :: uu____1018 in
                                      uu____1003 :: uu____1004 in
                                    let uu____1022 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____996
                                      uu____1022 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k in
                                let null_wp =
                                  let expected_k =
                                    let uu____1029 =
                                      let uu____1036 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      [uu____1036] in
                                    let uu____1037 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1029
                                      uu____1037 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1041 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1041 with
                                  | (t,uu____1047) ->
                                      let expected_k =
                                        let uu____1051 =
                                          let uu____1058 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1059 =
                                            let uu____1062 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1062] in
                                          uu____1058 :: uu____1059 in
                                        let uu____1063 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1051
                                          uu____1063 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1066 =
                                  let uu____1077 =
                                    let uu____1078 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1078.FStar_Syntax_Syntax.n in
                                  match uu____1077 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1093 ->
                                      let repr =
                                        let uu____1095 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1095 with
                                        | (t,uu____1101) ->
                                            let expected_k =
                                              let uu____1105 =
                                                let uu____1112 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1113 =
                                                  let uu____1116 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1116] in
                                                uu____1112 :: uu____1113 in
                                              let uu____1117 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1105 uu____1117 in
                                            tc_check_trivial_guard env1
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env1 repr in
                                        let uu____1130 =
                                          let uu____1133 =
                                            let uu____1134 =
                                              let uu____1149 =
                                                let uu____1152 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1153 =
                                                  let uu____1156 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1156] in
                                                uu____1152 :: uu____1153 in
                                              (repr1, uu____1149) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1134 in
                                          FStar_Syntax_Syntax.mk uu____1133 in
                                        uu____1130
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1171 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1171 wp in
                                      let destruct_repr t =
                                        let uu____1184 =
                                          let uu____1185 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1185.FStar_Syntax_Syntax.n in
                                        match uu____1184 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1196,(t1,uu____1198)::
                                             (wp,uu____1200)::[])
                                            -> (t1, wp)
                                        | uu____1243 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____1254 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____1254
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____1255 =
                                          fresh_effect_signature () in
                                        match uu____1255 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1271 =
                                                let uu____1278 =
                                                  let uu____1279 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1279 in
                                                [uu____1278] in
                                              let uu____1280 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____1271 uu____1280 in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b in
                                            let x_a =
                                              let uu____1286 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1286 in
                                            let wp_g_x =
                                              let uu____1290 =
                                                let uu____1291 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____1292 =
                                                  let uu____1293 =
                                                    let uu____1294 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1294 in
                                                  [uu____1293] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1291 uu____1292 in
                                              uu____1290
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____1303 =
                                                  let uu____1304 =
                                                    let uu____1305 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____1305
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____1314 =
                                                    let uu____1315 =
                                                      let uu____1318 =
                                                        let uu____1321 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____1322 =
                                                          let uu____1325 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____1326 =
                                                            let uu____1329 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____1330 =
                                                              let uu____1333
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____1333] in
                                                            uu____1329 ::
                                                              uu____1330 in
                                                          uu____1325 ::
                                                            uu____1326 in
                                                        uu____1321 ::
                                                          uu____1322 in
                                                      r :: uu____1318 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1315 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1304 uu____1314 in
                                                uu____1303
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let expected_k =
                                              let uu____1339 =
                                                let uu____1346 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1347 =
                                                  let uu____1350 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____1351 =
                                                    let uu____1354 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____1355 =
                                                      let uu____1358 =
                                                        let uu____1359 =
                                                          let uu____1360 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____1360 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1359 in
                                                      let uu____1361 =
                                                        let uu____1364 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____1365 =
                                                          let uu____1368 =
                                                            let uu____1369 =
                                                              let uu____1370
                                                                =
                                                                let uu____1377
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____1377] in
                                                              let uu____1378
                                                                =
                                                                let uu____1381
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1381 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1370
                                                                uu____1378 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1369 in
                                                          [uu____1368] in
                                                        uu____1364 ::
                                                          uu____1365 in
                                                      uu____1358 ::
                                                        uu____1361 in
                                                    uu____1354 :: uu____1355 in
                                                  uu____1350 :: uu____1351 in
                                                uu____1346 :: uu____1347 in
                                              let uu____1382 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____1339 uu____1382 in
                                            let uu____1385 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k in
                                            (match uu____1385 with
                                             | (expected_k1,uu____1393,uu____1394)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env3 =
                                                   let uu___66_1399 = env2 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___66_1399.FStar_TypeChecker_Env.dep_graph)
                                                   } in
                                                 let br =
                                                   check_and_gen' env3
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____1409 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1409 in
                                        let res =
                                          let wp =
                                            let uu____1416 =
                                              let uu____1417 =
                                                let uu____1418 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____1418
                                                  FStar_Pervasives_Native.snd in
                                              let uu____1427 =
                                                let uu____1428 =
                                                  let uu____1431 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____1432 =
                                                    let uu____1435 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____1435] in
                                                  uu____1431 :: uu____1432 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1428 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1417 uu____1427 in
                                            uu____1416
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____1441 =
                                            let uu____1448 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1449 =
                                              let uu____1452 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____1452] in
                                            uu____1448 :: uu____1449 in
                                          let uu____1453 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____1441
                                            uu____1453 in
                                        let uu____1456 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k in
                                        match uu____1456 with
                                        | (expected_k1,uu____1470,uu____1471)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____1475 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____1475 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1496 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos)) in
                                      let actions =
                                        let check_action act =
                                          let uu____1521 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ in
                                          match uu____1521 with
                                          | (act_typ,uu____1529,g_t) ->
                                              let env' =
                                                let uu___67_1532 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___67_1532.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___67_1532.FStar_TypeChecker_Env.dep_graph)
                                                } in
                                              ((let uu____1534 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED") in
                                                if uu____1534
                                                then
                                                  let uu____1535 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn in
                                                  let uu____1536 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____1535 uu____1536
                                                else ());
                                               (let uu____1538 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn in
                                                match uu____1538 with
                                                | (act_defn,uu____1546,g_a)
                                                    ->
                                                    let act_defn1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant]
                                                        env1 act_defn in
                                                    let act_typ1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant;
                                                        FStar_TypeChecker_Normalize.Eager_unfolding;
                                                        FStar_TypeChecker_Normalize.Beta]
                                                        env1 act_typ in
                                                    let uu____1550 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1 in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____1578 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c in
                                                          (match uu____1578
                                                           with
                                                           | (bs1,uu____1588)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun in
                                                               let k =
                                                                 let uu____1595
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____1595 in
                                                               let uu____1598
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k in
                                                               (match uu____1598
                                                                with
                                                                | (k1,uu____1610,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____1612 ->
                                                          let uu____1613 =
                                                            let uu____1618 =
                                                              let uu____1619
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2 in
                                                              let uu____1620
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____1619
                                                                uu____1620 in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____1618) in
                                                          FStar_Errors.raise_error
                                                            uu____1613
                                                            act_defn1.FStar_Syntax_Syntax.pos in
                                                    (match uu____1550 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k in
                                                         ((let uu____1629 =
                                                             let uu____1630 =
                                                               let uu____1631
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____1631 in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____1630 in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____1629);
                                                          (let act_typ2 =
                                                             let uu____1635 =
                                                               let uu____1636
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k in
                                                               uu____1636.FStar_Syntax_Syntax.n in
                                                             match uu____1635
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____1659
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                 (match uu____1659
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____1668
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____1668
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1690
                                                                    =
                                                                    let uu____1691
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____1691] in
                                                                    let uu____1692
                                                                    =
                                                                    let uu____1701
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____1701] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1690;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1692;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____1702
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1702))
                                                             | uu____1705 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)" in
                                                           let uu____1708 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1 in
                                                           match uu____1708
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ3 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ2 in
                                                               let act_typ4 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ3 in
                                                               let uu___68_1717
                                                                 = act in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___68_1717.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___68_1717.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___68_1717.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ4
                                                               }))))) in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action) in
                                      (repr, bind_repr, return_repr, actions) in
                                match uu____1066 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____1741 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____1741 in
                                    let uu____1744 =
                                      let uu____1751 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____1751 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____1772 ->
                                               let uu____1775 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           (FStar_Syntax_Syntax.order_univ_name
                                                              u1 u2)
                                                             =
                                                             (Prims.parse_int
                                                                "0"))
                                                      gen_univs
                                                      annotated_univ_names) in
                                               if uu____1775
                                               then (gen_univs, t)
                                               else
                                                 (let uu____1789 =
                                                    let uu____1794 =
                                                      let uu____1795 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names) in
                                                      let uu____1796 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs) in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____1795 uu____1796 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____1794) in
                                                  FStar_Errors.raise_error
                                                    uu____1789
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                    (match uu____1744 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____1810 =
                                             let uu____1815 =
                                               let uu____1816 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____1816.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____1815) in
                                           match uu____1810 with
                                           | ([],uu____1819) -> t
                                           | (uu____1830,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____1831,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____1849 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____1862 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____1862 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____1867 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____1869 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____1869))
                                                && (m <> n1) in
                                            if uu____1867
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____1885 =
                                                  FStar_Util.string_of_int m in
                                                let uu____1892 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____1893 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____1885 uu____1892
                                                  uu____1893 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____1901 =
                                             close1 (- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____1901 with
                                           | (univs2,defn) ->
                                               let uu____1908 =
                                                 close1
                                                   (- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____1908 with
                                                | (univs',typ) ->
                                                    let uu___69_1918 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___69_1918.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___69_1918.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___69_1918.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___70_1923 = ed2 in
                                           let uu____1924 =
                                             close1 (Prims.parse_int "0")
                                               return_wp in
                                           let uu____1925 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp in
                                           let uu____1926 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1 in
                                           let uu____1927 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp in
                                           let uu____1928 =
                                             close1 (Prims.parse_int "0")
                                               stronger in
                                           let uu____1929 =
                                             close1 (Prims.parse_int "1")
                                               close_wp in
                                           let uu____1930 =
                                             close1 (Prims.parse_int "0")
                                               assert_p in
                                           let uu____1931 =
                                             close1 (Prims.parse_int "0")
                                               assume_p in
                                           let uu____1932 =
                                             close1 (Prims.parse_int "0")
                                               null_wp in
                                           let uu____1933 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp in
                                           let uu____1934 =
                                             let uu____1935 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____1935 in
                                           let uu____1946 =
                                             close1 (Prims.parse_int "0")
                                               return_repr in
                                           let uu____1947 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr in
                                           let uu____1948 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___70_1923.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___70_1923.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____1924;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____1925;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____1926;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____1927;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____1928;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____1929;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____1930;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____1931;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____1932;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____1933;
                                             FStar_Syntax_Syntax.repr =
                                               uu____1934;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____1946;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____1947;
                                             FStar_Syntax_Syntax.actions =
                                               uu____1948
                                           } in
                                         ((let uu____1952 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____1952
                                           then
                                             let uu____1953 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____1953
                                           else ());
                                          ed3))))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____1971 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____1971 with
      | (effect_binders_un,signature_un) ->
          let uu____1988 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____1988 with
           | (effect_binders,env1,uu____2007) ->
               let uu____2008 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____2008 with
                | (signature,uu____2024) ->
                    let raise_error1 a uu____2035 =
                      match uu____2035 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2061  ->
                           match uu____2061 with
                           | (bv,qual) ->
                               let uu____2072 =
                                 let uu___71_2073 = bv in
                                 let uu____2074 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___71_2073.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___71_2073.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2074
                                 } in
                               (uu____2072, qual)) effect_binders in
                    let uu____2077 =
                      let uu____2084 =
                        let uu____2085 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2085.FStar_Syntax_Syntax.n in
                      Obj.magic
                        (match uu____2084 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2095)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2117 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature"))) in
                    (match uu____2077 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2135 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2135
                           then
                             let uu____2136 =
                               let uu____2139 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2139 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2136
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2173 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2173 with
                           | (t2,comp,uu____2186) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2193 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2193 with
                          | (repr,_comp) ->
                              ((let uu____2215 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2215
                                then
                                  let uu____2216 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2216
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____2222 =
                                    let uu____2223 =
                                      let uu____2224 =
                                        let uu____2239 =
                                          let uu____2246 =
                                            let uu____2251 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2252 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2251, uu____2252) in
                                          [uu____2246] in
                                        (wp_type1, uu____2239) in
                                      FStar_Syntax_Syntax.Tm_app uu____2224 in
                                    mk1 uu____2223 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2222 in
                                let effect_signature =
                                  let binders =
                                    let uu____2277 =
                                      let uu____2282 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2282) in
                                    let uu____2283 =
                                      let uu____2290 =
                                        let uu____2291 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2291
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2290] in
                                    uu____2277 :: uu____2283 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let effect_signature1 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1 in
                                  let uu____2354 = item in
                                  match uu____2354 with
                                  | (u_item,item1) ->
                                      let uu____2375 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2375 with
                                       | (item2,item_comp) ->
                                           ((let uu____2391 =
                                               let uu____2392 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2392 in
                                             if uu____2391
                                             then
                                               let uu____2393 =
                                                 let uu____2398 =
                                                   let uu____2399 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2400 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2399 uu____2400 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2398) in
                                               FStar_Errors.raise_err
                                                 uu____2393
                                             else ());
                                            (let uu____2402 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2402 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2422 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2422 with
                                | (dmff_env1,uu____2446,bind_wp,bind_elab) ->
                                    let uu____2449 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2449 with
                                     | (dmff_env2,uu____2473,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____2480 =
                                             let uu____2481 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2481.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____2480 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2525 =
                                                       let uu____2540 =
                                                         let uu____2545 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____2545 in
                                                       match uu____2540 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____2609 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity" in
                                                     match uu____2525 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____2648 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2 in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____2648
                                                             [b11; b21] in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____2665 =
                                                               let uu____2666
                                                                 =
                                                                 let uu____2681
                                                                   =
                                                                   let uu____2688
                                                                    =
                                                                    let uu____2693
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                    let uu____2694
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                    (uu____2693,
                                                                    uu____2694) in
                                                                   [uu____2688] in
                                                                 (wp_type1,
                                                                   uu____2681) in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____2666 in
                                                             mk1 uu____2665 in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1 in
                                                         let uu____2709 =
                                                           let uu____2718 =
                                                             let uu____2719 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1 in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____2719 in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____2718 in
                                                         (match uu____2709
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a415 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____2738
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____2740
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2 in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____2740
                                                                    (match what'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                                    raise_error1
                                                                    ()
                                                                    (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                    error_msg)))
                                                                  a415 in
                                                              ((match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                    then
                                                                    fail ()
                                                                    else ();
                                                                    (
                                                                    let uu____2746
                                                                    =
                                                                    FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()) in
                                                                    FStar_All.pipe_right
                                                                    uu____2746
                                                                    FStar_Pervasives.ignore)));
                                                               (let wp =
                                                                  let t2 =
                                                                    (FStar_Pervasives_Native.fst
                                                                    b21).FStar_Syntax_Syntax.sort in
                                                                  let pure_wp_type
                                                                    =
                                                                    FStar_TypeChecker_DMFF.double_star
                                                                    t2 in
                                                                  FStar_Syntax_Syntax.gen_bv
                                                                    "wp"
                                                                    FStar_Pervasives_Native.None
                                                                    pure_wp_type in
                                                                let body3 =
                                                                  let uu____2773
                                                                    =
                                                                    let uu____2774
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp in
                                                                    let uu____2775
                                                                    =
                                                                    let uu____2776
                                                                    =
                                                                    let uu____2783
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                    (uu____2783,
                                                                    FStar_Pervasives_Native.None) in
                                                                    [uu____2776] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____2774
                                                                    uu____2775 in
                                                                  uu____2773
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                let uu____2808
                                                                  =
                                                                  let uu____2809
                                                                    =
                                                                    let uu____2816
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp in
                                                                    [uu____2816] in
                                                                  b11 ::
                                                                    uu____2809 in
                                                                let uu____2821
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what in
                                                                FStar_Syntax_Util.abs
                                                                  uu____2808
                                                                  uu____2821
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____2822 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return"))) in
                                         let return_wp1 =
                                           let uu____2824 =
                                             let uu____2825 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2825.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____2824 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____2869 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____2869
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____2882 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return"))) in
                                         let bind_wp1 =
                                           let uu____2884 =
                                             let uu____2885 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____2885.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____2884 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (binders,body,what) ->
                                                  Obj.repr
                                                    (let r =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         FStar_Parser_Const.range_lid
                                                         (FStar_Syntax_Syntax.Delta_defined_at_level
                                                            (Prims.parse_int
                                                               "1"))
                                                         FStar_Pervasives_Native.None in
                                                     let uu____2912 =
                                                       let uu____2913 =
                                                         let uu____2916 =
                                                           let uu____2917 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r) in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____2917 in
                                                         [uu____2916] in
                                                       FStar_List.append
                                                         uu____2913 binders in
                                                     FStar_Syntax_Util.abs
                                                       uu____2912 body what)
                                              | uu____2918 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedBindShape,
                                                         "unexpected shape for bind"))) in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____2936 =
                                                let uu____2937 =
                                                  let uu____2938 =
                                                    let uu____2953 =
                                                      let uu____2954 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____2954 in
                                                    (t, uu____2953) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2938 in
                                                mk1 uu____2937 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2936) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____2984 = f a2 in
                                               [uu____2984]
                                           | x::xs ->
                                               let uu____2989 =
                                                 apply_last1 f xs in
                                               x :: uu____2989 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____3009 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3009 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3039 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3039
                                                 then
                                                   let uu____3040 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3040
                                                 else ());
                                                (let uu____3042 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3042))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3051 =
                                                 let uu____3056 = mk_lid name in
                                                 let uu____3057 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3056 uu____3057 in
                                               (match uu____3051 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3061 =
                                                        let uu____3064 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____3064 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3061);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3161 =
                                             let uu____3164 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3165 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3164 :: uu____3165 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3161);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3263 =
                                               let uu____3266 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3267 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3266 :: uu____3267 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3263);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3362 =
                                                FStar_List.fold_left
                                                  (fun uu____3402  ->
                                                     fun action  ->
                                                       match uu____3402 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3423 =
                                                             let uu____3430 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3430
                                                               params_un in
                                                           (match uu____3423
                                                            with
                                                            | (action_params,env',uu____3439)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3459
                                                                     ->
                                                                    match uu____3459
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3470
                                                                    =
                                                                    let uu___72_3471
                                                                    = bv in
                                                                    let uu____3472
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___72_3471.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___72_3471.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3472
                                                                    } in
                                                                    (uu____3470,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3476
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3476
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____3506
                                                                    ->
                                                                    let uu____3507
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3507 in
                                                                    ((
                                                                    let uu____3511
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____3511
                                                                    then
                                                                    let uu____3512
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____3513
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____3514
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____3515
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____3512
                                                                    uu____3513
                                                                    uu____3514
                                                                    uu____3515
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    let uu___73_3523
                                                                    = action in
                                                                    let uu____3524
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____3525
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___73_3523.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___73_3523.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___73_3523.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____3524;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____3525
                                                                    } in
                                                                    uu____3522
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____3519))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3362 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____3558 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____3559 =
                                                        let uu____3562 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____3562] in
                                                      uu____3558 ::
                                                        uu____3559 in
                                                    let uu____3563 =
                                                      let uu____3564 =
                                                        let uu____3565 =
                                                          let uu____3566 =
                                                            let uu____3581 =
                                                              let uu____3588
                                                                =
                                                                let uu____3593
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____3594
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____3593,
                                                                  uu____3594) in
                                                              [uu____3588] in
                                                            (repr,
                                                              uu____3581) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____3566 in
                                                        mk1 uu____3565 in
                                                      let uu____3609 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____3564
                                                        uu____3609 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____3563
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____3612 =
                                                    let uu____3619 =
                                                      let uu____3620 =
                                                        let uu____3623 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____3623 in
                                                      uu____3620.FStar_Syntax_Syntax.n in
                                                    Obj.magic
                                                      (match uu____3619 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____3633)
                                                           ->
                                                           Obj.repr
                                                             (let uu____3662
                                                                =
                                                                let uu____3679
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1 in
                                                                match uu____3679
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____3737
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity" in
                                                              match uu____3662
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____3787
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3791
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3791 in
                                                                    uu____3788.FStar_Syntax_Syntax.n in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____3787
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3816
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                    match uu____3816
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3829
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3854
                                                                     ->
                                                                    match uu____3854
                                                                    with
                                                                    | 
                                                                    (bv,uu____3860)
                                                                    ->
                                                                    let uu____3861
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____3862
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____3861
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____3829
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3926 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3931
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3939 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____3944
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____3947
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____3944,
                                                                    uu____3947)))
                                                                    | 
                                                                    uu____3954
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____3955
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3961 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3960) in
                                                                    raise_error1
                                                                    ()
                                                                    uu____3955)))
                                                       | uu____3962 ->
                                                           Obj.repr
                                                             (let uu____3963
                                                                =
                                                                let uu____3968
                                                                  =
                                                                  let uu____3969
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1 in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____3969 in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____3968) in
                                                              raise_error1 ()
                                                                uu____3963)) in
                                                  (match uu____3612 with
                                                   | (pre,post) ->
                                                       ((let uu____3987 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____3989 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____3991 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___74_3993 =
                                                             ed in
                                                           let uu____3994 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____3995 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____3996 =
                                                             let uu____3997 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____3997) in
                                                           let uu____4004 =
                                                             let uu____4005 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4005) in
                                                           let uu____4012 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____4013 =
                                                             let uu____4014 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4014) in
                                                           let uu____4021 =
                                                             let uu____4022 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4022) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3994;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3995;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____3996;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4004;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___74_3993.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4012;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4013;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4021;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____4029 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4029
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4047
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4047
                                                               then
                                                                 let uu____4048
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4048
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4072) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4063 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4060;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4087
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4087
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4089
                                                                 =
                                                                 let uu____4092
                                                                   =
                                                                   let uu____4095
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4095 in
                                                                 FStar_List.append
                                                                   uu____4092
                                                                   sigelts' in
                                                               (uu____4089,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4152 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4152 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4185 = FStar_List.hd ses in
            uu____4185.FStar_Syntax_Syntax.sigrng in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____4190 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4195,uu____4196);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4198;
               FStar_Syntax_Syntax.sigattrs = uu____4199;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4203);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4205;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4206;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4210);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4212;
                 FStar_Syntax_Syntax.sigattrs = uu____4213;_}::[]
               when
               ((_0_40 = (Prims.parse_int "0")) &&
                  (_0_41 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r) in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1) in
               let lex_top_t =
                 let uu____4278 =
                   let uu____4281 =
                     let uu____4282 =
                       let uu____4289 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4289, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4282 in
                   FStar_Syntax_Syntax.mk uu____4281 in
                 uu____4278 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let lex_cons_t =
                 let a =
                   let uu____4307 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4307 in
                 let hd1 =
                   let uu____4309 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4309 in
                 let tl1 =
                   let uu____4311 =
                     let uu____4312 =
                       let uu____4315 =
                         let uu____4316 =
                           let uu____4323 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4323, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4316 in
                       FStar_Syntax_Syntax.mk uu____4315 in
                     uu____4312 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4311 in
                 let res =
                   let uu____4332 =
                     let uu____4335 =
                       let uu____4336 =
                         let uu____4343 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4343,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4336 in
                     FStar_Syntax_Syntax.mk uu____4335 in
                   uu____4332 FStar_Pervasives_Native.None r2 in
                 let uu____4349 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4349 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let uu____4388 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4388;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4393 ->
               let err_msg =
                 let uu____4397 =
                   let uu____4398 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4398 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4397 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
let tc_assume:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r in
            let uu____4423 = FStar_Syntax_Util.type_u () in
            match uu____4423 with
            | (k,uu____4429) ->
                let phi1 =
                  let uu____4431 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4431
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4433 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4433 with
                  | (us,phi2) ->
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us, phi2));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs = []
                      }))
let tc_inductive:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____4475 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4475 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____4508 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____4508 FStar_List.flatten in
              ((let uu____4522 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____4522
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
                          let uu____4533 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____4543,uu____4544,uu____4545,uu____4546,uu____4547)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____4556 -> failwith "Impossible!" in
                          match uu____4533 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____4567 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____4571,uu____4572,uu____4573,uu____4574,uu____4575)
                        -> lid
                    | uu____4584 -> failwith "Impossible" in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let res =
                  let uu____4602 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____4602
                  then ([sig_bndle], data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume in
                     let uu____4625 =
                       let uu____4628 =
                         let uu____4629 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____4629;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____4628 :: ses1 in
                     (uu____4625, data_ops_ses)) in
                (let uu____4639 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____4673 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____4698 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____4750 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____4750 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], []))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____4788 = cps_and_elaborate env1 ne in
           (match uu____4788 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___75_4825 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___75_4825.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___75_4825.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___75_4825.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___75_4825.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___76_4827 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___76_4827.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___76_4827.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___76_4827.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___76_4827.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___77_4835 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___77_4835.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___77_4835.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___77_4835.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___77_4835.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____4843 =
             let uu____4850 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____4850 in
           (match uu____4843 with
            | (a,wp_a_src) ->
                let uu____4865 =
                  let uu____4872 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____4872 in
                (match uu____4865 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____4888 =
                         let uu____4891 =
                           let uu____4892 =
                             let uu____4899 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____4899) in
                           FStar_Syntax_Syntax.NT uu____4892 in
                         [uu____4891] in
                       FStar_Syntax_Subst.subst uu____4888 wp_b_tgt in
                     let expected_k =
                       let uu____4903 =
                         let uu____4910 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____4911 =
                           let uu____4914 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____4914] in
                         uu____4910 :: uu____4911 in
                       let uu____4915 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____4903 uu____4915 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____4936 =
                           let uu____4941 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____4941) in
                         let uu____4942 =
                           FStar_TypeChecker_Env.get_range env1 in
                         FStar_Errors.raise_error uu____4936 uu____4942 in
                       let uu____4945 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____4945 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____4977 =
                             let uu____4978 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____4978 in
                           if uu____4977
                           then no_reify eff_name
                           else
                             (let uu____4984 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____4985 =
                                let uu____4988 =
                                  let uu____4989 =
                                    let uu____5004 =
                                      let uu____5007 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5008 =
                                        let uu____5011 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5011] in
                                      uu____5007 :: uu____5008 in
                                    (repr, uu____5004) in
                                  FStar_Syntax_Syntax.Tm_app uu____4989 in
                                FStar_Syntax_Syntax.mk uu____4988 in
                              uu____4985 FStar_Pervasives_Native.None
                                uu____4984) in
                     let uu____5017 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5045,lift_wp)) ->
                           let uu____5069 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5069)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5095 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5095
                             then
                               let uu____5096 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5096
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange) in
                             let uu____5099 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5099 with
                             | (lift1,comp,uu____5114) ->
                                 let uu____5115 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5115 with
                                  | (uu____5128,lift_wp,lift_elab) ->
                                      let uu____5131 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5132 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5017 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___78_5173 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___78_5173.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___78_5173.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___78_5173.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___78_5173.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___78_5173.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___78_5173.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___78_5173.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___78_5173.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___78_5173.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___78_5173.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___78_5173.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___78_5173.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___78_5173.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___78_5173.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___78_5173.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___78_5173.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___78_5173.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___78_5173.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___78_5173.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___78_5173.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___78_5173.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___78_5173.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___78_5173.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___78_5173.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___78_5173.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___78_5173.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___78_5173.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___78_5173.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___78_5173.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___78_5173.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___78_5173.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___78_5173.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___78_5173.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___78_5173.FStar_TypeChecker_Env.dep_graph)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5179,lift1)
                                ->
                                let uu____5191 =
                                  let uu____5198 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5198 in
                                (match uu____5191 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv
                                         FStar_Pervasives_Native.None
                                         wp_a_src1 in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1 in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2
                                           (FStar_Pervasives_Native.snd
                                              lift_wp) in
                                       let lift_wp_a =
                                         let uu____5222 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5223 =
                                           let uu____5226 =
                                             let uu____5227 =
                                               let uu____5242 =
                                                 let uu____5245 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5246 =
                                                   let uu____5249 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5249] in
                                                 uu____5245 :: uu____5246 in
                                               (lift_wp1, uu____5242) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5227 in
                                           FStar_Syntax_Syntax.mk uu____5226 in
                                         uu____5223
                                           FStar_Pervasives_Native.None
                                           uu____5222 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5258 =
                                         let uu____5265 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5266 =
                                           let uu____5269 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5270 =
                                             let uu____5273 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5273] in
                                           uu____5269 :: uu____5270 in
                                         uu____5265 :: uu____5266 in
                                       let uu____5274 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5258
                                         uu____5274 in
                                     let uu____5277 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5277 with
                                      | (expected_k2,uu____5287,uu____5288)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___79_5291 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___79_5291.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___79_5291.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___80_5293 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___80_5293.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___80_5293.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___80_5293.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___80_5293.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5312 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5312 with
            | (tps1,c1) ->
                let uu____5327 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5327 with
                 | (tps2,env3,us) ->
                     let uu____5345 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5345 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5366 =
                              let uu____5367 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5367 in
                            match uu____5366 with
                            | (uvs1,t) ->
                                let uu____5382 =
                                  let uu____5395 =
                                    let uu____5400 =
                                      let uu____5401 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5401.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5400) in
                                  match uu____5395 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5416,c4)) -> ([], c4)
                                  | (uu____5456,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____5483 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5382 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____5527 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____5527 with
                                         | (uu____5532,t1) ->
                                             let uu____5534 =
                                               let uu____5539 =
                                                 let uu____5540 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     lid in
                                                 let uu____5541 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.length uvs1)
                                                     FStar_Util.string_of_int in
                                                 let uu____5542 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1 in
                                                 FStar_Util.format3
                                                   "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                   uu____5540 uu____5541
                                                   uu____5542 in
                                               (FStar_Errors.Fatal_TooManyUniverse,
                                                 uu____5539) in
                                             FStar_Errors.raise_error
                                               uu____5534 r)
                                      else ();
                                      (let se1 =
                                         let uu___81_5545 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags1));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___81_5545.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___81_5545.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___81_5545.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___81_5545.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____5562,uu____5563,uu____5564) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5568  ->
                   match uu___56_5568 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5569 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____5574,uu____5575) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___56_5583  ->
                   match uu___56_5583 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____5584 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____5594 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____5594
             then
               let uu____5595 =
                 let uu____5600 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid) in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____5600) in
               FStar_Errors.raise_error uu____5595 r
             else ());
            (let uu____5602 =
               if uvs = []
               then
                 let uu____5603 =
                   let uu____5604 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____5604 in
                 check_and_gen env2 t uu____5603
               else
                 (let uu____5610 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____5610 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____5618 =
                          let uu____5619 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____5619 in
                        tc_check_trivial_guard env2 t1 uu____5618 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____5625 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____5625)) in
             match uu____5602 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___82_5641 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___82_5641.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___82_5641.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___82_5641.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___82_5641.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____5651 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____5651 with
            | (uu____5664,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____5674 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____5674 with
            | (e1,c,g1) ->
                let uu____5692 =
                  let uu____5699 =
                    let uu____5702 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____5702 in
                  let uu____5703 =
                    let uu____5708 = FStar_Syntax_Syntax.lcomp_comp c in
                    (e1, uu____5708) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____5699 uu____5703 in
                (match uu____5692 with
                 | (e2,uu____5718,g) ->
                     ((let uu____5721 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____5721);
                      (let se1 =
                         let uu___83_5723 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___83_5723.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___83_5723.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___83_5723.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___83_5723.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____5774 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____5774
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____5782 =
                      let uu____5787 =
                        let uu____5788 = FStar_Syntax_Print.lid_to_string l in
                        let uu____5789 = FStar_Syntax_Print.quals_to_string q in
                        let uu____5790 =
                          FStar_Syntax_Print.quals_to_string q' in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____5788 uu____5789 uu____5790 in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____5787) in
                    FStar_Errors.raise_error uu____5782 r) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____5816 =
                   let uu____5817 = FStar_Syntax_Subst.compress def in
                   uu____5817.FStar_Syntax_Syntax.n in
                 match uu____5816 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____5827,uu____5828)
                     -> binders
                 | uu____5849 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____5859;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____5937) -> val_bs1
                     | (uu____5960,[]) -> val_bs1
                     | ((body_bv,uu____5984)::bt,(val_bv,aqual)::vt) ->
                         let uu____6021 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6037) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___84_6039 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___85_6042 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___85_6042.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___84_6039.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___84_6039.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6021 in
                   let uu____6043 =
                     let uu____6046 =
                       let uu____6047 =
                         let uu____6060 = rename_binders1 def_bs val_bs in
                         (uu____6060, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6047 in
                     FStar_Syntax_Syntax.mk uu____6046 in
                   uu____6043 FStar_Pervasives_Native.None r1
               | uu____6078 -> typ1 in
             let uu___86_6079 = lb in
             let uu____6080 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___86_6079.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___86_6079.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6080;
               FStar_Syntax_Syntax.lbeff =
                 (uu___86_6079.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___86_6079.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___86_6079.FStar_Syntax_Syntax.lbattrs)
             } in
           let uu____6083 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6134  ->
                     fun lb  ->
                       match uu____6134 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6176 =
                             let uu____6187 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6187 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____6272 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____6315 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6315, quals_opt1))) in
                           (match uu____6176 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6083 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6409 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___57_6413  ->
                                match uu___57_6413 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6414 -> false)) in
                      if uu____6409
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6424 =
                    let uu____6427 =
                      let uu____6428 =
                        let uu____6441 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6441) in
                      FStar_Syntax_Syntax.Tm_let uu____6428 in
                    FStar_Syntax_Syntax.mk uu____6427 in
                  uu____6424 FStar_Pervasives_Native.None r in
                let uu____6459 =
                  let uu____6470 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___87_6479 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___87_6479.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___87_6479.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___87_6479.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___87_6479.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___87_6479.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___87_6479.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___87_6479.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___87_6479.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___87_6479.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___87_6479.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___87_6479.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___87_6479.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___87_6479.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___87_6479.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___87_6479.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___87_6479.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___87_6479.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___87_6479.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___87_6479.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___87_6479.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___87_6479.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___87_6479.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___87_6479.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___87_6479.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___87_6479.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___87_6479.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___87_6479.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___87_6479.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___87_6479.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___87_6479.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___87_6479.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___87_6479.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___87_6479.FStar_TypeChecker_Env.dep_graph)
                       }) e in
                  match uu____6470 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____6492;
                       FStar_Syntax_Syntax.vars = uu____6493;_},uu____6494,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____6523 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____6523) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____6541,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____6546 -> quals in
                      ((let uu___88_6554 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___88_6554.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___88_6554.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___88_6554.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____6563 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6459 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____6612 = log env2 in
                       if uu____6612
                       then
                         let uu____6613 =
                           let uu____6614 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____6629 =
                                         let uu____6638 =
                                           let uu____6639 =
                                             let uu____6642 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____6642.FStar_Syntax_Syntax.fv_name in
                                           uu____6639.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____6638 in
                                       match uu____6629 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____6649 -> false in
                                     if should_log
                                     then
                                       let uu____6658 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____6659 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____6658 uu____6659
                                     else "")) in
                           FStar_All.pipe_right uu____6614
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____6613
                       else ());
                      (let reified_tactic_type l t =
                         let t1 = FStar_Syntax_Subst.compress t in
                         match t1.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                             let uu____6690 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____6690 with
                              | (bs1,c1) ->
                                  let uu____6697 =
                                    FStar_Syntax_Util.is_total_comp c1 in
                                  if uu____6697
                                  then
                                    let c' =
                                      match c1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Total (t',u) ->
                                          let uu____6709 =
                                            let uu____6710 =
                                              FStar_Syntax_Subst.compress t' in
                                            uu____6710.FStar_Syntax_Syntax.n in
                                          (match uu____6709 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (h,args) ->
                                               let uu____6735 =
                                                 let uu____6736 =
                                                   FStar_Syntax_Subst.compress
                                                     h in
                                                 uu____6736.FStar_Syntax_Syntax.n in
                                               (match uu____6735 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (h',u') ->
                                                    let h'' =
                                                      let uu____6746 =
                                                        FStar_Syntax_Syntax.lid_as_fv
                                                          FStar_Parser_Const.u_tac_lid
                                                          FStar_Syntax_Syntax.Delta_constant
                                                          FStar_Pervasives_Native.None in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.fv_to_tm
                                                        uu____6746 in
                                                    let uu____6747 =
                                                      let uu____6748 =
                                                        let uu____6749 =
                                                          FStar_Syntax_Syntax.mk_Tm_uinst
                                                            h'' u' in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____6749 args in
                                                      uu____6748
                                                        FStar_Pervasives_Native.None
                                                        t'.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      uu____6747 u
                                                | uu____6752 -> c1)
                                           | uu____6753 -> c1)
                                      | uu____6754 -> c1 in
                                    let uu___89_6755 = t1 in
                                    let uu____6756 =
                                      let uu____6757 =
                                        let uu____6770 =
                                          FStar_Syntax_Subst.close_comp bs1
                                            c' in
                                        (bs1, uu____6770) in
                                      FStar_Syntax_Syntax.Tm_arrow uu____6757 in
                                    {
                                      FStar_Syntax_Syntax.n = uu____6756;
                                      FStar_Syntax_Syntax.pos =
                                        (uu___89_6755.FStar_Syntax_Syntax.pos);
                                      FStar_Syntax_Syntax.vars =
                                        (uu___89_6755.FStar_Syntax_Syntax.vars)
                                    }
                                  else t1)
                         | FStar_Syntax_Syntax.Tm_app (h,args) ->
                             let uu____6794 =
                               let uu____6795 = FStar_Syntax_Subst.compress h in
                               uu____6795.FStar_Syntax_Syntax.n in
                             (match uu____6794 with
                              | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                  let h'' =
                                    let uu____6805 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        FStar_Parser_Const.u_tac_lid
                                        FStar_Syntax_Syntax.Delta_constant
                                        FStar_Pervasives_Native.None in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.fv_to_tm uu____6805 in
                                  let uu____6806 =
                                    let uu____6807 =
                                      FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6807
                                      args in
                                  uu____6806 FStar_Pervasives_Native.None
                                    t1.FStar_Syntax_Syntax.pos
                              | uu____6810 -> t1)
                         | uu____6811 -> t1 in
                       let reified_tactic_decl assm_lid lb =
                         let t =
                           reified_tactic_type assm_lid
                             lb.FStar_Syntax_Syntax.lbtyp in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (assm_lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                  t));
                           FStar_Syntax_Syntax.sigrng =
                             (FStar_Ident.range_of_lid assm_lid);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       let reflected_tactic_decl b lb bs assm_lid comp =
                         let reified_tac =
                           let uu____6839 =
                             FStar_Syntax_Syntax.lid_as_fv assm_lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm
                             uu____6839 in
                         let tac_args =
                           FStar_List.map
                             (fun x  ->
                                let uu____6856 =
                                  FStar_Syntax_Syntax.bv_to_name
                                    (FStar_Pervasives_Native.fst x) in
                                (uu____6856, (FStar_Pervasives_Native.snd x)))
                             bs in
                         let reflect_head =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                (FStar_Const.Const_reflect
                                   FStar_Parser_Const.tac_effect_lid))
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let refl_arg =
                           FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let app =
                           FStar_Syntax_Syntax.mk_Tm_app reflect_head
                             [(refl_arg, FStar_Pervasives_Native.None)]
                             FStar_Pervasives_Native.None
                             FStar_Range.dummyRange in
                         let unit_binder =
                           let uu____6887 =
                             FStar_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStar_Syntax_Syntax.t_unit in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                             uu____6887 in
                         let body =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs [unit_binder] app)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let func =
                           FStar_All.pipe_left
                             (FStar_Syntax_Util.abs bs body)
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                         let uu___90_6894 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let
                                ((b,
                                   [(let uu___91_6906 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___91_6906.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___91_6906.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___91_6906.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___91_6906.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = func;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___91_6906.FStar_Syntax_Syntax.lbattrs)
                                     })]), lids));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___90_6894.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___90_6894.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___90_6894.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___90_6894.FStar_Syntax_Syntax.sigattrs)
                         } in
                       let tactic_decls =
                         match FStar_Pervasives_Native.snd lbs1 with
                         | hd1::[] ->
                             let uu____6923 =
                               FStar_Syntax_Util.arrow_formals_comp
                                 hd1.FStar_Syntax_Syntax.lbtyp in
                             (match uu____6923 with
                              | (bs,comp) ->
                                  let t = FStar_Syntax_Util.comp_result comp in
                                  let uu____6957 =
                                    let uu____6958 =
                                      FStar_Syntax_Subst.compress t in
                                    uu____6958.FStar_Syntax_Syntax.n in
                                  (match uu____6957 with
                                   | FStar_Syntax_Syntax.Tm_app (h,args) ->
                                       let h1 = FStar_Syntax_Subst.compress h in
                                       let tac_lid =
                                         let uu____6991 =
                                           let uu____6994 =
                                             FStar_Util.right
                                               hd1.FStar_Syntax_Syntax.lbname in
                                           uu____6994.FStar_Syntax_Syntax.fv_name in
                                         uu____6991.FStar_Syntax_Syntax.v in
                                       let assm_lid =
                                         let uu____6996 =
                                           FStar_All.pipe_left
                                             FStar_Ident.id_of_text
                                             (Prims.strcat "__"
                                                (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                                         FStar_Ident.lid_of_ns_and_id
                                           tac_lid.FStar_Ident.ns uu____6996 in
                                       let uu____6997 =
                                         get_tactic_fv env2 assm_lid h1 in
                                       (match uu____6997 with
                                        | FStar_Pervasives_Native.Some fv ->
                                            let uu____7007 =
                                              let uu____7008 =
                                                let uu____7009 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env2 tac_lid in
                                                FStar_All.pipe_left
                                                  FStar_Util.is_some
                                                  uu____7009 in
                                              Prims.op_Negation uu____7008 in
                                            if uu____7007
                                            then
                                              ((let uu____7039 =
                                                  let uu____7040 =
                                                    is_builtin_tactic
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  Prims.op_Negation
                                                    uu____7040 in
                                                if uu____7039
                                                then
                                                  let added_modules =
                                                    FStar_ST.op_Bang
                                                      user_tactics_modules in
                                                  let module_name =
                                                    FStar_Ident.ml_path_of_lid
                                                      env2.FStar_TypeChecker_Env.curmodule in
                                                  (if
                                                     Prims.op_Negation
                                                       (FStar_List.contains
                                                          module_name
                                                          added_modules)
                                                   then
                                                     FStar_ST.op_Colon_Equals
                                                       user_tactics_modules
                                                       (FStar_List.append
                                                          added_modules
                                                          [module_name])
                                                   else ())
                                                else ());
                                               (let uu____7093 =
                                                  env2.FStar_TypeChecker_Env.is_native_tactic
                                                    assm_lid in
                                                if uu____7093
                                                then
                                                  let se_assm =
                                                    reified_tactic_decl
                                                      assm_lid hd1 in
                                                  let se_refl =
                                                    reflected_tactic_decl
                                                      (FStar_Pervasives_Native.fst
                                                         lbs1) hd1 bs
                                                      assm_lid comp in
                                                  FStar_Pervasives_Native.Some
                                                    (se_assm, se_refl)
                                                else
                                                  FStar_Pervasives_Native.None))
                                            else FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7122 ->
                                       FStar_Pervasives_Native.None))
                         | uu____7127 -> FStar_Pervasives_Native.None in
                       match tactic_decls with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7149 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7149
                             then
                               let uu____7150 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7151 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7150 uu____7151
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___58_7202  ->
                match uu___58_7202 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7203 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7209) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7215 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7224 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7229 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7254 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7278) ->
          let uu____7287 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7287
          then
            let for_export_bundle se1 uu____7318 =
              match uu____7318 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7357,uu____7358) ->
                       let dec =
                         let uu___92_7368 = se1 in
                         let uu____7369 =
                           let uu____7370 =
                             let uu____7377 =
                               let uu____7380 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7380 in
                             (l, us, uu____7377) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7370 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7369;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7368.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7368.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7368.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7392,uu____7393,uu____7394) ->
                       let dec =
                         let uu___93_7400 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___93_7400.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___93_7400.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___93_7400.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7405 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7427,uu____7428,uu____7429) ->
          let uu____7430 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7430 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7451 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7451
          then
            ([(let uu___94_7467 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___94_7467.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___94_7467.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___94_7467.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7469 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___59_7473  ->
                       match uu___59_7473 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7474 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7479 -> true
                       | uu____7480 -> false)) in
             if uu____7469 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7498 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7503 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7508 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7513 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7518 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7536) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7553 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7553
          then ([], hidden)
          else
            (let dec =
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7584 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7584
          then
            let uu____7593 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___95_7606 = se in
                      let uu____7607 =
                        let uu____7608 =
                          let uu____7615 =
                            let uu____7616 =
                              let uu____7619 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7619.FStar_Syntax_Syntax.fv_name in
                            uu____7616.FStar_Syntax_Syntax.v in
                          (uu____7615, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7608 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7607;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___95_7606.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___95_7606.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___95_7606.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7593, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7639 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7656 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7671) ->
          let env1 =
            let uu____7675 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7675 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7677 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7678 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7688 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7688) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7689,uu____7690,uu____7691) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7695  ->
                  match uu___60_7695 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7696 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7697,uu____7698) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___60_7706  ->
                  match uu___60_7706 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7707 -> false))
          -> env
      | uu____7708 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7768 se =
        match uu____7768 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7821 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7821
              then
                let uu____7822 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7822
              else ());
             (let uu____7824 = tc_decl env1 se in
              match uu____7824 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7874 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7874
                             then
                               let uu____7875 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7875
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  (FStar_TypeChecker_Env.promote_id_info env1
                     (fun t  ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                          FStar_TypeChecker_Normalize.CheckNoUvars;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.NoDeltaSteps;
                          FStar_TypeChecker_Normalize.CompressUvars;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Zeta;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Iota;
                          FStar_TypeChecker_Normalize.NoFullNorm] env1 t);
                   (let env2 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env2  ->
                              fun se1  -> add_sigelt_to_env env2 se1) env1) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____7898 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7898
                     then
                       let uu____7899 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7905 =
                                  let uu____7906 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7906 "\n" in
                                Prims.strcat s uu____7905) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7899
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7911 =
                       let accum_exports_hidden uu____7941 se1 =
                         match uu____7941 with
                         | (exports1,hidden1) ->
                             let uu____7969 = for_export hidden1 se1 in
                             (match uu____7969 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7911 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___96_8048 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___96_8048.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___96_8048.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___96_8048.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___96_8048.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8126 = acc in
        match uu____8126 with
        | (uu____8161,uu____8162,env1,uu____8164) ->
            let uu____8177 =
              FStar_Util.record_time
                (fun uu____8223  -> process_one_decl acc se) in
            (match uu____8177 with
             | (r,ms_elapsed) ->
                 ((let uu____8287 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8287
                   then
                     let uu____8288 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8289 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8288 uu____8289
                   else ());
                  r)) in
      let uu____8291 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8291 with
      | (ses1,exports,env1,uu____8339) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun push_before_typechecking  ->
        let verify =
          FStar_Options.should_verify
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
        let action = if verify then "Verifying" else "Lax-checking" in
        let label1 =
          if modul.FStar_Syntax_Syntax.is_interface
          then "interface"
          else "implementation" in
        (let uu____8379 = FStar_Options.debug_any () in
         if uu____8379
         then
           FStar_Util.print3 "%s %s of %s\n" action label1
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         else ());
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
         let msg = Prims.strcat "Internals for " name in
         let env1 =
           let uu___97_8385 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___97_8385.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___97_8385.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___97_8385.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___97_8385.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___97_8385.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___97_8385.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___97_8385.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___97_8385.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___97_8385.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___97_8385.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___97_8385.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___97_8385.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___97_8385.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___97_8385.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___97_8385.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___97_8385.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___97_8385.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___97_8385.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___97_8385.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___97_8385.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___97_8385.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___97_8385.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___97_8385.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___97_8385.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___97_8385.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___97_8385.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___97_8385.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___97_8385.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___97_8385.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___97_8385.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___97_8385.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___97_8385.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___97_8385.FStar_TypeChecker_Env.dep_graph)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8389 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8389 with
          | (ses,exports,env3) ->
              ((let uu___98_8422 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___98_8422.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___98_8422.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___98_8422.FStar_Syntax_Syntax.is_interface)
                }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____8444 = tc_decls env decls in
        match uu____8444 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___99_8475 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___99_8475.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___99_8475.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___99_8475.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___100_8492 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___100_8492.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___100_8492.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___100_8492.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___100_8492.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___100_8492.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___100_8492.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___100_8492.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___100_8492.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___100_8492.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___100_8492.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___100_8492.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___100_8492.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___100_8492.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___100_8492.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___100_8492.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___100_8492.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___100_8492.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___100_8492.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___100_8492.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___100_8492.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___100_8492.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___100_8492.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___100_8492.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___100_8492.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___100_8492.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___100_8492.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___100_8492.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___100_8492.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___100_8492.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___100_8492.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___100_8492.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___100_8492.FStar_TypeChecker_Env.dep_graph)
          } in
        let check_term1 lid univs1 t =
          let uu____8503 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8503 with
          | (univs2,t1) ->
              ((let uu____8511 =
                  let uu____8512 =
                    let uu____8515 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8515 in
                  FStar_All.pipe_left uu____8512
                    (FStar_Options.Other "Exports") in
                if uu____8511
                then
                  let uu____8516 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8517 =
                    let uu____8518 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8518
                      (FStar_String.concat ", ") in
                  let uu____8527 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8516 uu____8517 uu____8527
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8530 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8530 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8554 =
             let uu____8555 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8556 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8555 uu____8556 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8554);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8563) ->
              let uu____8572 =
                let uu____8573 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8573 in
              if uu____8572
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8583,uu____8584) ->
              let t =
                let uu____8596 =
                  let uu____8599 =
                    let uu____8600 =
                      let uu____8613 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8613) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8600 in
                  FStar_Syntax_Syntax.mk uu____8599 in
                uu____8596 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8620,uu____8621,uu____8622) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8630 =
                let uu____8631 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8631 in
              if uu____8630 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8635,lbs),uu____8637) ->
              let uu____8652 =
                let uu____8653 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8653 in
              if uu____8652
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term2
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags1) ->
              let uu____8672 =
                let uu____8673 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8673 in
              if uu____8672
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8680 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8681 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8688 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8689 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8690 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8691 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelts ->
          (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun must_check_exports  ->
    fun env  ->
      fun modul  ->
        fun exports  ->
          let modul1 =
            let uu___101_8710 = modul in
            {
              FStar_Syntax_Syntax.name =
                (uu___101_8710.FStar_Syntax_Syntax.name);
              FStar_Syntax_Syntax.declarations =
                (uu___101_8710.FStar_Syntax_Syntax.declarations);
              FStar_Syntax_Syntax.exports = exports;
              FStar_Syntax_Syntax.is_interface =
                (modul.FStar_Syntax_Syntax.is_interface)
            } in
          let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
          (let uu____8713 =
             (let uu____8716 = FStar_Options.lax () in
              Prims.op_Negation uu____8716) && must_check_exports in
           if uu____8713 then check_exports env1 modul1 exports else ());
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
            (Prims.strcat "Ending modul "
               (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
            env1 modul1;
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
            ();
          (let uu____8722 =
             let uu____8723 = FStar_Options.interactive () in
             Prims.op_Negation uu____8723 in
           if uu____8722
           then
             let uu____8724 = FStar_Options.restore_cmd_line_options true in
             FStar_All.pipe_right uu____8724 FStar_Pervasives.ignore
           else ());
          (modul1, env1)
let load_checked_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      let env1 =
        FStar_TypeChecker_Env.set_current_module env
          modul.FStar_Syntax_Syntax.name in
      (let uu____8734 =
         let uu____8735 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         Prims.strcat "Internals for " uu____8735 in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
         uu____8734);
      (let env2 =
         FStar_List.fold_left
           (fun env2  ->
              fun se  ->
                let env3 = FStar_TypeChecker_Env.push_sigelt env2 se in
                let lids = FStar_Syntax_Util.lids_of_sigelt se in
                FStar_All.pipe_right lids
                  (FStar_List.iter
                     (fun lid  ->
                        let uu____8754 =
                          FStar_TypeChecker_Env.try_lookup_lid env3 lid in
                        ()));
                env3) env1 modul.FStar_Syntax_Syntax.declarations in
       let uu____8775 =
         finish_partial_modul false env2 modul
           modul.FStar_Syntax_Syntax.exports in
       FStar_Pervasives_Native.snd uu____8775)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let uu____8790 = tc_partial_modul env modul true in
      match uu____8790 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul true env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      (let uu____8821 = FStar_Options.debug_any () in
       if uu____8821
       then
         let uu____8822 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8822
       else ());
      (let env1 =
         let uu___102_8826 = env in
         let uu____8827 =
           let uu____8828 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8828 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___102_8826.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___102_8826.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___102_8826.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___102_8826.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___102_8826.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___102_8826.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___102_8826.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___102_8826.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___102_8826.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___102_8826.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___102_8826.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___102_8826.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___102_8826.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___102_8826.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___102_8826.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___102_8826.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___102_8826.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___102_8826.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8827;
           FStar_TypeChecker_Env.lax_universes =
             (uu___102_8826.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___102_8826.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___102_8826.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___102_8826.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___102_8826.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___102_8826.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___102_8826.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___102_8826.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___102_8826.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___102_8826.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___102_8826.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___102_8826.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___102_8826.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___102_8826.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___102_8826.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___102_8826.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____8829 = tc_modul env1 m in
       match uu____8829 with
       | (m1,env2) ->
           ((let uu____8841 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8841
             then
               let uu____8842 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8842
             else ());
            (let uu____8845 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8845
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____8876 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8876 with
                       | (univnames1,e) ->
                           let uu___103_8883 = lb in
                           let uu____8884 =
                             let uu____8887 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____8887 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___103_8883.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___103_8883.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___103_8883.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___103_8883.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____8884;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___103_8883.FStar_Syntax_Syntax.lbattrs)
                           } in
                     let uu___104_8888 = se in
                     let uu____8889 =
                       let uu____8890 =
                         let uu____8897 =
                           let uu____8904 = FStar_List.map update lbs in
                           (b, uu____8904) in
                         (uu____8897, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____8890 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____8889;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___104_8888.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___104_8888.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___104_8888.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___104_8888.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____8917 -> se in
               let normalized_module =
                 let uu___105_8919 = m1 in
                 let uu____8920 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___105_8919.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____8920;
                   FStar_Syntax_Syntax.exports =
                     (uu___105_8919.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___105_8919.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____8921 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____8921
             else ());
            (m1, env2)))