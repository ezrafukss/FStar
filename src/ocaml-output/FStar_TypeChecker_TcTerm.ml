open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___64_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___64_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___64_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___64_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___64_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___64_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___64_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___64_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___64_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___64_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___64_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___64_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___64_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___64_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___64_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___64_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___64_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___64_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___64_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___64_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___64_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___64_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___64_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___64_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___64_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___64_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___64_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___64_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___64_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___64_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___64_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___64_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___64_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___64_4.FStar_TypeChecker_Env.dep_graph)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___65_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___65_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___65_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___65_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___65_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___65_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___65_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___65_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___65_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___65_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___65_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___65_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___65_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___65_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___65_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___65_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___65_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___65_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___65_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___65_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___65_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___65_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___65_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___65_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___65_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___65_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___65_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___65_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___65_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___65_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___65_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___65_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___65_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___65_8.FStar_TypeChecker_Env.dep_graph)
    }
let mk_lex_list:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v1  ->
         fun tl1  ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos in
           let uu____40 =
             let uu____41 =
               let uu____42 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____43 =
                 let uu____46 = FStar_Syntax_Syntax.as_arg tl1 in [uu____46] in
               uu____42 :: uu____43 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____41 in
           uu____40 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___59_53  ->
    match uu___59_53 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____56 -> false
let steps:
  'Auu____61 . 'Auu____61 -> FStar_TypeChecker_Normalize.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.Eager_unfolding]
let norm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let norm_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let check_no_escape:
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> t
            | uu____107 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____115 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____115 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____125 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____127 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____127
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____129 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____130 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____129 uu____130 in
                          let uu____131 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____131 in
                        let s =
                          let uu____133 =
                            let uu____134 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____134 in
                          FStar_TypeChecker_Util.new_uvar env uu____133 in
                        let uu____143 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____143 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____148 -> fail ())) in
          aux false kt
let push_binding:
  'Auu____154 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____154) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let maybe_extend_subst:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____184 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____184
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___66_198 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___66_198.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___66_198.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____201  ->
             let uu____202 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____202 t)
      }
let memo_tk:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> e
let value_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____245 = FStar_Syntax_Syntax.mk_Total t in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____245
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____254 =
            let uu____261 = FStar_TypeChecker_Env.expected_typ env in
            match uu____261 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____272 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____272
                  then
                    let uu____273 = FStar_Syntax_Print.term_to_string t in
                    let uu____274 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____273
                      uu____274
                  else ());
                 (let uu____276 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____276 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____292 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____292 with
                       | (e2,g) ->
                           ((let uu____306 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____306
                             then
                               let uu____307 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____308 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____309 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____310 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____307 uu____308 uu____309 uu____310
                             else ());
                            (let msg =
                               let uu____317 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____317
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____334 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____334 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____254 with
          | (e1,lc1,g) ->
              ((let uu____357 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____357
                then
                  let uu____358 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____358
                else ());
               (e1, lc1, g))
let comp_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____381 = FStar_TypeChecker_Env.expected_typ env in
        match uu____381 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____391 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____391 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let check_expected_effect:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun copt  ->
      fun uu____424  ->
        match uu____424 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____453 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____453
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____455 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____455
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____457 =
              match copt with
              | FStar_Pervasives_Native.Some uu____470 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____473 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____475 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____475)) in
                  if uu____473
                  then
                    let uu____482 =
                      let uu____485 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____485 in
                    (uu____482, c)
                  else
                    (let uu____489 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____489
                     then
                       let uu____496 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____496)
                     else
                       (let uu____500 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____500
                        then
                          let uu____507 =
                            let uu____510 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____510 in
                          (uu____507, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____457 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e (FStar_Syntax_Util.lcomp_of_comp c2) in
                      let c4 = c3.FStar_Syntax_Syntax.comp () in
                      let uu____540 =
                        FStar_TypeChecker_Util.check_comp env e c4 expected_c in
                      (match uu____540 with
                       | (e1,uu____554,g) ->
                           let g1 =
                             let uu____557 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____557
                               "could not prove post-condition" g in
                           ((let uu____559 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____559
                             then
                               let uu____560 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____561 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____560 uu____561
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c4)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c4) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____568 'Auu____569 .
    FStar_TypeChecker_Env.env ->
      ('Auu____569,'Auu____568,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____569,'Auu____568,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____589  ->
      match uu____589 with
      | (te,kt,f) ->
          let uu____599 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____599 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____607 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____612 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____607 uu____612)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____622 = FStar_TypeChecker_Env.expected_typ env in
    match uu____622 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____626 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____626
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____650 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____650 with
      | (head1,args) ->
          let uu____689 =
            let uu____690 = FStar_Syntax_Util.un_uinst head1 in
            uu____690.FStar_Syntax_Syntax.n in
          (match uu____689 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____697 = FStar_List.tl args in
               get_pat_vars_args uu____697 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____706 ->
               let uu____707 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____707)
and get_pat_vars_args:
  FStar_Syntax_Syntax.args ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun args  ->
    fun acc  ->
      FStar_List.fold_left
        (fun s  ->
           fun arg  -> get_pat_vars (FStar_Pervasives_Native.fst arg) s) acc
        args
let check_smt_pat:
  'Auu____737 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____737) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____770 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____770
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____771;
                  FStar_Syntax_Syntax.effect_name = uu____772;
                  FStar_Syntax_Syntax.result_typ = uu____773;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____777)::[];
                  FStar_Syntax_Syntax.flags = uu____778;_}
                ->
                let pat_vars =
                  let uu____826 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____827 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____826 uu____827 in
                let uu____830 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____857  ->
                          match uu____857 with
                          | (b,uu____863) ->
                              let uu____864 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____864)) in
                (match uu____830 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____870) ->
                     let uu____875 =
                       let uu____880 =
                         let uu____881 = FStar_Syntax_Print.bv_to_string x in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____881 in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____880) in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____875)
            | uu____882 -> failwith "Impossible"
          else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
          FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___67_932 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___67_932.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___67_932.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___67_932.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___67_932.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___67_932.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___67_932.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___67_932.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___67_932.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___67_932.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___67_932.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___67_932.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___67_932.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___67_932.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___67_932.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___67_932.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___67_932.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___67_932.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___67_932.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___67_932.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___67_932.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___67_932.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___67_932.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___67_932.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___67_932.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___67_932.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___67_932.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___67_932.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___67_932.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___67_932.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___67_932.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___67_932.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___67_932.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___67_932.FStar_TypeChecker_Env.dep_graph)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____948 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____948
               then
                 let uu____949 = FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____950 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n" uu____949
                   uu____950
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____969  ->
                         match uu____969 with
                         | (b,uu____977) ->
                             let t =
                               let uu____979 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____979 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____982 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____983 -> []
                              | uu____996 ->
                                  let uu____997 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____997]))) in
               let as_lex_list dec =
                 let uu____1002 = FStar_Syntax_Util.head_and_args dec in
                 match uu____1002 with
                 | (head1,uu____1018) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1040 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____1044 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___60_1053  ->
                         match uu___60_1053 with
                         | FStar_Syntax_Syntax.DECREASES uu____1054 -> true
                         | uu____1057 -> false)) in
               match uu____1044 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1061 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   (match xs with | x::[] -> x | uu____1070 -> mk_lex_list xs)) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____1091 =
              match uu____1091 with
              | (l,t,u_names) ->
                  let uu____1109 =
                    let uu____1110 = FStar_Syntax_Subst.compress t in
                    uu____1110.FStar_Syntax_Syntax.n in
                  (match uu____1109 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1171  ->
                                 match uu____1171 with
                                 | (x,imp) ->
                                     let uu____1182 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____1182
                                     then
                                       let uu____1187 =
                                         let uu____1188 =
                                           let uu____1191 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____1191 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1188
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____1187, imp)
                                     else (x, imp))) in
                       let uu____1193 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____1193 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____1212 =
                                let uu____1213 =
                                  let uu____1214 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____1215 =
                                    let uu____1218 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____1218] in
                                  uu____1214 :: uu____1215 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1213 in
                              uu____1212 FStar_Pervasives_Native.None r in
                            let uu____1221 = FStar_Util.prefix formals2 in
                            (match uu____1221 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___68_1268 = last1 in
                                   let uu____1269 =
                                     FStar_Syntax_Util.refine last1 precedes1 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___68_1268.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___68_1268.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1269
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____1295 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____1295
                                   then
                                     let uu____1296 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____1297 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____1298 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1296 uu____1297 uu____1298
                                   else ());
                                  (l, t', u_names))))
                   | uu____1302 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos) in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
let rec tc_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___69_1753 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___69_1753.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___69_1753.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___69_1753.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___69_1753.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___69_1753.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___69_1753.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___69_1753.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___69_1753.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___69_1753.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___69_1753.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___69_1753.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___69_1753.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___69_1753.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___69_1753.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___69_1753.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___69_1753.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___69_1753.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___69_1753.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___69_1753.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___69_1753.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___69_1753.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___69_1753.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___69_1753.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___69_1753.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___69_1753.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___69_1753.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___69_1753.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___69_1753.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___69_1753.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___69_1753.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___69_1753.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___69_1753.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___69_1753.FStar_TypeChecker_Env.dep_graph)
         }) e
and tc_maybe_toplevel_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      (let uu____1765 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1765
       then
         let uu____1766 =
           let uu____1767 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1767 in
         let uu____1768 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1766 uu____1768
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1777 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1808 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1815 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1832 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1833 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1834 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1835 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1836 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1853 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1866 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1873 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1874;
              FStar_Syntax_Syntax.vars = uu____1875;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1876,uu____1877,ty))
           ->
           let uu____1887 =
             let uu____1888 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1888 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1887, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1894 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1894 with
            | (e2,c,g) ->
                let g1 =
                  let uu___70_1911 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___70_1911.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___70_1911.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___70_1911.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____1912 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____1912, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1933 = FStar_Syntax_Util.type_u () in
           (match uu____1933 with
            | (t,u) ->
                let uu____1946 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1946 with
                 | (e2,c,g) ->
                     let uu____1962 =
                       let uu____1977 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1977 with
                       | (env2,uu____1999) -> tc_pats env2 pats in
                     (match uu____1962 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___71_2033 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___71_2033.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___71_2033.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___71_2033.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2034 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2037 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2034, c, uu____2037))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2045 =
             let uu____2046 = FStar_Syntax_Subst.compress e1 in
             uu____2046.FStar_Syntax_Syntax.n in
           (match uu____2045 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2055,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2057;
                               FStar_Syntax_Syntax.lbtyp = uu____2058;
                               FStar_Syntax_Syntax.lbeff = uu____2059;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2084 =
                  let uu____2091 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2091 e11 in
                (match uu____2084 with
                 | (e12,c1,g1) ->
                     let uu____2101 = tc_term env1 e2 in
                     (match uu____2101 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2) in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c1.FStar_Syntax_Syntax.res_typ in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.eff_name
                              c2.FStar_Syntax_Syntax.res_typ in
                          let e3 =
                            let uu____2125 =
                              let uu____2128 =
                                let uu____2129 =
                                  let uu____2142 =
                                    let uu____2149 =
                                      let uu____2152 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2152] in
                                    (false, uu____2149) in
                                  (uu____2142, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2129 in
                              FStar_Syntax_Syntax.mk uu____2128 in
                            uu____2125 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2174 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2174)))
            | uu____2177 ->
                let uu____2178 = tc_term env1 e1 in
                (match uu____2178 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2200) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2212) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2231 = tc_term env1 e1 in
           (match uu____2231 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2255) ->
           let uu____2302 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2302 with
            | (env0,uu____2316) ->
                let uu____2321 = tc_comp env0 expected_c in
                (match uu____2321 with
                 | (expected_c1,uu____2335,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2340 =
                       let uu____2347 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2347 e1 in
                     (match uu____2340 with
                      | (e2,c',g') ->
                          let uu____2357 =
                            let uu____2364 =
                              let uu____2369 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2369) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2364 in
                          (match uu____2357 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____2418 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2418 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2427 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2427) in
                               let uu____2428 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2428 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2448) ->
           let uu____2495 = FStar_Syntax_Util.type_u () in
           (match uu____2495 with
            | (k,u) ->
                let uu____2508 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2508 with
                 | (t1,uu____2522,f) ->
                     let uu____2524 =
                       let uu____2531 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2531 e1 in
                     (match uu____2524 with
                      | (e2,c,g) ->
                          let uu____2541 =
                            let uu____2546 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2550  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2546 e2 c f in
                          (match uu____2541 with
                           | (c1,f1) ->
                               let uu____2559 =
                                 let uu____2566 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2566 c1 in
                               (match uu____2559 with
                                | (e3,c2,f2) ->
                                    let uu____2606 =
                                      let uu____2607 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2607 in
                                    (e3, c2, uu____2606))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2608;
              FStar_Syntax_Syntax.vars = uu____2609;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2672 = FStar_Syntax_Util.head_and_args top in
           (match uu____2672 with
            | (unary_op,uu____2694) ->
                let head1 =
                  let uu____2718 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2718 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2756;
              FStar_Syntax_Syntax.vars = uu____2757;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2820 = FStar_Syntax_Util.head_and_args top in
           (match uu____2820 with
            | (unary_op,uu____2842) ->
                let head1 =
                  let uu____2866 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2866 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2904);
              FStar_Syntax_Syntax.pos = uu____2905;
              FStar_Syntax_Syntax.vars = uu____2906;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2969 = FStar_Syntax_Util.head_and_args top in
           (match uu____2969 with
            | (unary_op,uu____2991) ->
                let head1 =
                  let uu____3015 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3015 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3053;
              FStar_Syntax_Syntax.vars = uu____3054;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3130 = FStar_Syntax_Util.head_and_args top in
           (match uu____3130 with
            | (unary_op,uu____3152) ->
                let head1 =
                  let uu____3176 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3176 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3220;
              FStar_Syntax_Syntax.vars = uu____3221;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3259 =
             let uu____3266 =
               let uu____3267 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3267 in
             tc_term uu____3266 e1 in
           (match uu____3259 with
            | (e2,c,g) ->
                let uu____3291 = FStar_Syntax_Util.head_and_args top in
                (match uu____3291 with
                 | (head1,uu____3313) ->
                     let uu____3334 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3361 =
                       let uu____3362 =
                         let uu____3365 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3365 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3362 in
                     (uu____3334, uu____3361, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3370;
              FStar_Syntax_Syntax.vars = uu____3371;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3424 = FStar_Syntax_Util.head_and_args top in
           (match uu____3424 with
            | (head1,uu____3446) ->
                let env' =
                  let uu____3468 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3468 in
                let uu____3469 = tc_term env' a1 in
                (match uu____3469 with
                 | (e1,uu____3483,g1) ->
                     let uu____3485 = tc_term env1 a2 in
                     (match uu____3485 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3502 =
                            let uu____3505 =
                              let uu____3506 =
                                let uu____3507 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3508 =
                                  let uu____3511 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3511] in
                                uu____3507 :: uu____3508 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3506 in
                            uu____3505 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3502, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3516;
              FStar_Syntax_Syntax.vars = uu____3517;_},uu____3518)
           ->
           let uu____3539 =
             let uu____3544 =
               let uu____3545 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____3545 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3544) in
           FStar_Errors.raise_error uu____3539 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3552;
              FStar_Syntax_Syntax.vars = uu____3553;_},uu____3554)
           ->
           let uu____3575 =
             let uu____3580 =
               let uu____3581 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____3581 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3580) in
           FStar_Errors.raise_error uu____3575 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3588;
              FStar_Syntax_Syntax.vars = uu____3589;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3622 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____3622 with
             | (env0,uu____3636) ->
                 let uu____3641 = tc_term env0 e1 in
                 (match uu____3641 with
                  | (e2,c,g) ->
                      let uu____3657 = FStar_Syntax_Util.head_and_args top in
                      (match uu____3657 with
                       | (reify_op,uu____3679) ->
                           let u_c =
                             let uu____3701 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ in
                             match uu____3701 with
                             | (uu____3708,c',uu____3710) ->
                                 let uu____3711 =
                                   let uu____3712 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ in
                                   uu____3712.FStar_Syntax_Syntax.n in
                                 (match uu____3711 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3716 ->
                                      let uu____3717 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____3717 with
                                       | (t,u) ->
                                           let g_opt =
                                             FStar_TypeChecker_Rel.try_teq
                                               true env1
                                               c'.FStar_Syntax_Syntax.res_typ
                                               t in
                                           ((match g_opt with
                                             | FStar_Pervasives_Native.Some
                                                 g' ->
                                                 FStar_TypeChecker_Rel.force_trivial_guard
                                                   env1 g'
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 let uu____3729 =
                                                   let uu____3730 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c' in
                                                   let uu____3731 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ in
                                                   let uu____3732 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3730 uu____3731
                                                     uu____3732 in
                                                 failwith uu____3729);
                                            u))) in
                           let repr =
                             let uu____3734 = c.FStar_Syntax_Syntax.comp () in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3734
                               u_c in
                           let e3 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app
                                  (reify_op, [(e2, aqual)]))
                               FStar_Pervasives_Native.None
                               top.FStar_Syntax_Syntax.pos in
                           let c1 =
                             let uu____3755 =
                               FStar_Syntax_Syntax.mk_Total repr in
                             FStar_All.pipe_right uu____3755
                               FStar_Syntax_Util.lcomp_of_comp in
                           let uu____3756 =
                             comp_check_expected_typ env1 e3 c1 in
                           (match uu____3756 with
                            | (e4,c2,g') ->
                                let uu____3772 =
                                  FStar_TypeChecker_Rel.conj_guard g g' in
                                (e4, c2, uu____3772))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3774;
              FStar_Syntax_Syntax.vars = uu____3775;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____3817 =
               let uu____3818 =
                 let uu____3823 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____3823) in
               FStar_Errors.raise_error uu____3818 e1.FStar_Syntax_Syntax.pos in
             let uu____3830 = FStar_Syntax_Util.head_and_args top in
             match uu____3830 with
             | (reflect_op,uu____3852) ->
                 let uu____3873 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3873 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3906 =
                        let uu____3907 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3907 in
                      if uu____3906
                      then no_reflect ()
                      else
                        (let uu____3917 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3917 with
                         | (env_no_ex,topt) ->
                             let uu____3936 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3956 =
                                   let uu____3959 =
                                     let uu____3960 =
                                       let uu____3975 =
                                         let uu____3978 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3979 =
                                           let uu____3982 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3982] in
                                         uu____3978 :: uu____3979 in
                                       (repr, uu____3975) in
                                     FStar_Syntax_Syntax.Tm_app uu____3960 in
                                   FStar_Syntax_Syntax.mk uu____3959 in
                                 uu____3956 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3988 =
                                 let uu____3995 =
                                   let uu____3996 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____3996
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____3995 t in
                               match uu____3988 with
                               | (t1,uu____4024,g) ->
                                   let uu____4026 =
                                     let uu____4027 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4027.FStar_Syntax_Syntax.n in
                                   (match uu____4026 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4042,(res,uu____4044)::
                                         (wp,uu____4046)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4089 -> failwith "Impossible") in
                             (match uu____3936 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4120 =
                                    let uu____4125 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4125 with
                                    | (e2,c,g) ->
                                        ((let uu____4140 =
                                            let uu____4141 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4141 in
                                          if uu____4140
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4155 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4155 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4163 =
                                                  let uu____4172 =
                                                    let uu____4179 =
                                                      let uu____4180 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4181 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4180 uu____4181 in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4179,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4172] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4163);
                                               (let uu____4194 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4194)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4196 =
                                                let uu____4197 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4197 in
                                              (e2, uu____4196))) in
                                  (match uu____4120 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4207 =
                                           let uu____4208 =
                                             let uu____4209 =
                                               let uu____4210 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4210] in
                                             let uu____4211 =
                                               let uu____4220 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4220] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4209;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4211;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4208 in
                                         FStar_All.pipe_right uu____4207
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4240 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4240 with
                                        | (e4,c1,g') ->
                                            let uu____4256 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4256))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4303 =
               let uu____4304 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4304 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4303 instantiate_both in
           ((let uu____4320 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4320
             then
               let uu____4321 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4322 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4321
                 uu____4322
             else ());
            (let isquote =
               let uu____4325 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4325 with
               | (head2,uu____4341) ->
                   let uu____4362 =
                     let uu____4363 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4363.FStar_Syntax_Syntax.n in
                   (match uu____4362 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4367 -> false) in
             let uu____4368 = tc_term (no_inst env2) head1 in
             match uu____4368 with
             | (head2,chead,g_head) ->
                 let uu____4384 =
                   let uu____4391 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4391
                   then
                     let uu____4398 =
                       let uu____4405 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4405 in
                     match uu____4398 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4420 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4420) in
                 (match uu____4384 with
                  | (e1,c,g) ->
                      ((let uu____4433 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4433
                        then
                          let uu____4434 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4434
                        else ());
                       (let uu____4436 = comp_check_expected_typ env0 e1 c in
                        match uu____4436 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4453 =
                                let uu____4454 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4454.FStar_Syntax_Syntax.n in
                              match uu____4453 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4458) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___72_4520 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___72_4520.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___72_4520.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___72_4520.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4569 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4571 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4571 in
                            ((let uu____4573 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4573
                              then
                                let uu____4574 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4575 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4574 uu____4575
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4615 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4615 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4635 = tc_term env12 e1 in
                (match uu____4635 with
                 | (e11,c1,g1) ->
                     let uu____4651 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4661 = FStar_Syntax_Util.type_u () in
                           (match uu____4661 with
                            | (k,uu____4671) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4673 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4673, res_t)) in
                     (match uu____4651 with
                      | (env_branches,res_t) ->
                          ((let uu____4683 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4683
                            then
                              let uu____4684 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4684
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4794 =
                              let uu____4799 =
                                FStar_List.fold_right
                                  (fun uu____4871  ->
                                     fun uu____4872  ->
                                       match (uu____4871, uu____4872) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5077 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5077)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4799 with
                              | (cases,g) ->
                                  let uu____5168 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____5168, g) in
                            match uu____4794 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches) in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____5282  ->
                                              match uu____5282 with
                                              | ((pat,wopt,br),uu____5318,eff_label,uu____5320,uu____5321,uu____5322)
                                                  ->
                                                  let uu____5343 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t in
                                                  (pat, wopt, uu____5343))) in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_Syntax_Syntax.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos in
                                  let uu____5398 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5398
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5405 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5405 in
                                     let lb =
                                       let uu____5409 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.res_typ);
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____5409;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5413 =
                                         let uu____5416 =
                                           let uu____5417 =
                                             let uu____5430 =
                                               let uu____5431 =
                                                 let uu____5432 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5432] in
                                               FStar_Syntax_Subst.close
                                                 uu____5431 e_match in
                                             ((false, [lb]), uu____5430) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5417 in
                                         FStar_Syntax_Syntax.mk uu____5416 in
                                       uu____5413
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5445 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5445
                                  then
                                    let uu____5446 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5447 =
                                      let uu____5448 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5448 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5446 uu____5447
                                  else ());
                                 (let uu____5450 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5450))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5453;
                FStar_Syntax_Syntax.lbunivs = uu____5454;
                FStar_Syntax_Syntax.lbtyp = uu____5455;
                FStar_Syntax_Syntax.lbeff = uu____5456;
                FStar_Syntax_Syntax.lbdef = uu____5457;_}::[]),uu____5458)
           ->
           ((let uu____5478 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5478
             then
               let uu____5479 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5479
             else ());
            (let uu____5481 = FStar_Options.use_two_phase_tc () in
             if uu____5481
             then
               let is_lb_unannotated t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let
                     ((uu____5492,lb::[]),uu____5494) ->
                     let uu____5507 =
                       let uu____5508 =
                         FStar_Syntax_Subst.compress
                           lb.FStar_Syntax_Syntax.lbtyp in
                       uu____5508.FStar_Syntax_Syntax.n in
                     uu____5507 = FStar_Syntax_Syntax.Tm_unknown
                 | uu____5511 -> failwith "Impossible" in
               let drop_lbtyp t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let ((t1,lb::[]),t2) ->
                     let uu___73_5531 = t in
                     let uu____5532 =
                       let uu____5533 =
                         let uu____5546 =
                           let uu____5553 =
                             let uu____5556 =
                               let uu___74_5557 = lb in
                               let uu____5558 =
                                 FStar_Syntax_Syntax.mk
                                   FStar_Syntax_Syntax.Tm_unknown
                                   FStar_Pervasives_Native.None
                                   (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.pos in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___74_5557.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___74_5557.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = uu____5558;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___74_5557.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___74_5557.FStar_Syntax_Syntax.lbdef)
                               } in
                             [uu____5556] in
                           (t1, uu____5553) in
                         (uu____5546, t2) in
                       FStar_Syntax_Syntax.Tm_let uu____5533 in
                     {
                       FStar_Syntax_Syntax.n = uu____5532;
                       FStar_Syntax_Syntax.pos =
                         (uu___73_5531.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___73_5531.FStar_Syntax_Syntax.vars)
                     }
                 | uu____5571 -> failwith "Impossible" in
               let uu____5572 =
                 check_top_level_let
                   (let uu___75_5581 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___75_5581.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___75_5581.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___75_5581.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___75_5581.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___75_5581.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___75_5581.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___75_5581.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___75_5581.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___75_5581.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___75_5581.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___75_5581.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___75_5581.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___75_5581.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___75_5581.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___75_5581.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___75_5581.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___75_5581.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___75_5581.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___75_5581.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___75_5581.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___75_5581.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___75_5581.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___75_5581.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___75_5581.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___75_5581.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___75_5581.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___75_5581.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___75_5581.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___75_5581.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___75_5581.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___75_5581.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___75_5581.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___75_5581.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5572 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   ((let uu____5593 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____5593
                     then
                       let uu____5594 =
                         FStar_Syntax_Print.term_to_string lax_top1 in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5594
                     else ());
                    (let uu____5596 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5596
                     then
                       let uu____5603 =
                         let uu____5604 = is_lb_unannotated top in
                         if uu____5604 then drop_lbtyp lax_top1 else lax_top1 in
                       check_top_level_let env1 uu____5603
                     else (lax_top1, l, g)))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5608),uu____5609) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5624;
                FStar_Syntax_Syntax.lbunivs = uu____5625;
                FStar_Syntax_Syntax.lbtyp = uu____5626;
                FStar_Syntax_Syntax.lbeff = uu____5627;
                FStar_Syntax_Syntax.lbdef = uu____5628;_}::uu____5629),uu____5630)
           ->
           ((let uu____5652 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5652
             then
               let uu____5653 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5653
             else ());
            (let uu____5655 = FStar_Options.use_two_phase_tc () in
             if uu____5655
             then
               let uu____5662 =
                 check_top_level_let_rec
                   (let uu___76_5671 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___76_5671.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___76_5671.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___76_5671.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___76_5671.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___76_5671.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___76_5671.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___76_5671.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___76_5671.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___76_5671.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___76_5671.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___76_5671.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___76_5671.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___76_5671.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___76_5671.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___76_5671.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___76_5671.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___76_5671.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___76_5671.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___76_5671.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___76_5671.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___76_5671.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___76_5671.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___76_5671.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___76_5671.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___76_5671.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___76_5671.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___76_5671.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___76_5671.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___76_5671.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___76_5671.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___76_5671.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___76_5671.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___76_5671.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5662 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   ((let uu____5683 =
                       FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TwoPhases") in
                     if uu____5683
                     then
                       let uu____5684 =
                         FStar_Syntax_Print.term_to_string lax_top1 in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5684
                     else ());
                    (let uu____5686 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5686
                     then check_top_level_let_rec env1 lax_top1
                     else (lax_top1, l, g)))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5695),uu____5696) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        let uu____5722 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5812))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5872))::(uu____5873,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5874))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5947 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng in
        match uu____5722 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6031 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____6031 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6037 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6037) in
            let uu____6040 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____6040 with
             | (env',uu____6054) ->
                 let uu____6059 = tc_term env' typ in
                 (match uu____6059 with
                  | (typ1,uu____6073,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6076 = tc_tactic env' tau in
                        match uu____6076 with
                        | (tau1,uu____6090,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6098 =
                                    let uu____6099 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____6100 =
                                      let uu____6101 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____6101] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6099
                                      uu____6100 in
                                  uu____6098 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____6107 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____6107
                                    then
                                      let uu____6108 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____6108
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6111 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____6111)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___77_6115 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___77_6115.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___77_6115.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___77_6115.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___77_6115.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___77_6115.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___77_6115.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___77_6115.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___77_6115.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___77_6115.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___77_6115.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___77_6115.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___77_6115.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___77_6115.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___77_6115.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___77_6115.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___77_6115.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___77_6115.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___77_6115.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___77_6115.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___77_6115.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___77_6115.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___77_6115.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___77_6115.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___77_6115.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___77_6115.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___77_6115.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___77_6115.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___77_6115.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___77_6115.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___77_6115.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___77_6115.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___77_6115.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___77_6115.FStar_TypeChecker_Env.dep_graph)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit
and tc_reified_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___78_6119 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___78_6119.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___78_6119.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___78_6119.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___78_6119.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___78_6119.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___78_6119.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___78_6119.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___78_6119.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___78_6119.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___78_6119.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___78_6119.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___78_6119.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___78_6119.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___78_6119.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___78_6119.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___78_6119.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___78_6119.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___78_6119.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___78_6119.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___78_6119.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___78_6119.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___78_6119.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___78_6119.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___78_6119.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___78_6119.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___78_6119.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___78_6119.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___78_6119.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___78_6119.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___78_6119.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___78_6119.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___78_6119.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___78_6119.FStar_TypeChecker_Env.dep_graph)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____6135 = tc_tactic env tactic in
          (match uu____6135 with
           | (tactic1,uu____6145,uu____6146) ->
               FStar_Pervasives_Native.Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____6185 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____6185 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____6206 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____6206
              then FStar_Util.Inl t1
              else
                (let uu____6212 =
                   let uu____6213 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6213 in
                 FStar_Util.Inr uu____6212) in
            let is_data_ctor uu___61_6223 =
              match uu___61_6223 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6226) -> true
              | uu____6233 -> false in
            let uu____6236 =
              (is_data_ctor dc) &&
                (let uu____6238 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____6238) in
            if uu____6236
            then
              let uu____6245 =
                let uu____6250 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6250) in
              let uu____6251 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____6245 uu____6251
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6268 =
            let uu____6269 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6269 in
          failwith uu____6268
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6303 =
              let uu____6304 = FStar_Syntax_Subst.compress t1 in
              uu____6304.FStar_Syntax_Syntax.n in
            match uu____6303 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6307 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6320 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___79_6358 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___79_6358.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___79_6358.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___79_6358.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6410 =
            let uu____6423 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6423 with
            | FStar_Pervasives_Native.None  ->
                let uu____6438 = FStar_Syntax_Util.type_u () in
                (match uu____6438 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6410 with
           | (t,uu____6475,g0) ->
               let uu____6489 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6489 with
                | (e1,uu____6509,g1) ->
                    let uu____6523 =
                      let uu____6524 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6524
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6525 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6523, uu____6525)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6527 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6540 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6540)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6527 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___80_6559 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___80_6559.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___80_6559.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6562 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6562 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6583 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6583
                       then FStar_Util.Inl t1
                       else
                         (let uu____6589 =
                            let uu____6590 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6590 in
                          FStar_Util.Inr uu____6589) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6596;
             FStar_Syntax_Syntax.vars = uu____6597;_},uu____6598)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6603 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6603
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6611 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6611
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6619;
             FStar_Syntax_Syntax.vars = uu____6620;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6629 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6629 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6652 =
                     let uu____6657 =
                       let uu____6658 = FStar_Syntax_Print.fv_to_string fv in
                       let uu____6659 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____6660 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6658 uu____6659 uu____6660 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6657) in
                   let uu____6661 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____6652 uu____6661)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6677 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6681 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6681 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6683 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6683 with
           | ((us,t),range) ->
               ((let uu____6706 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6706
                 then
                   let uu____6707 =
                     let uu____6708 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6708 in
                   let uu____6709 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6710 = FStar_Range.string_of_range range in
                   let uu____6711 = FStar_Range.string_of_use_range range in
                   let uu____6712 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6707 uu____6709 uu____6710 uu____6711 uu____6712
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6717 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6717 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6741 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6741 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6755 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6755 with
                | (env2,uu____6769) ->
                    let uu____6774 = tc_binders env2 bs1 in
                    (match uu____6774 with
                     | (bs2,env3,g,us) ->
                         let uu____6793 = tc_comp env3 c1 in
                         (match uu____6793 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___81_6812 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___81_6812.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___81_6812.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6821 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6821 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____6840 =
            let uu____6845 =
              let uu____6846 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6846] in
            FStar_Syntax_Subst.open_term uu____6845 phi in
          (match uu____6840 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6856 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6856 with
                | (env2,uu____6870) ->
                    let uu____6875 =
                      let uu____6888 = FStar_List.hd x1 in
                      tc_binder env2 uu____6888 in
                    (match uu____6875 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6916 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6916
                           then
                             let uu____6917 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6918 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6919 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6917 uu____6918 uu____6919
                           else ());
                          (let uu____6921 = FStar_Syntax_Util.type_u () in
                           match uu____6921 with
                           | (t_phi,uu____6933) ->
                               let uu____6934 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6934 with
                                | (phi2,uu____6948,f2) ->
                                    let e1 =
                                      let uu___82_6953 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___82_6953.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___82_6953.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6960 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6960 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6973) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6996 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6996
            then
              let uu____6997 =
                FStar_Syntax_Print.term_to_string
                  (let uu___83_7000 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___83_7000.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___83_7000.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6997
            else ());
           (let uu____7006 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____7006 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____7019 ->
          let uu____7020 =
            let uu____7021 = FStar_Syntax_Print.term_to_string top in
            let uu____7022 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7021
              uu____7022 in
          failwith uu____7020
and tc_constant:
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7032 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7033,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7044,FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____7060 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7065 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7066 ->
            let uu____7067 =
              let uu____7072 =
                FStar_ToSyntax_Env.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____7072 FStar_Util.must in
            FStar_All.pipe_right uu____7067 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7097 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7098 =
              let uu____7103 =
                let uu____7104 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7104 in
              (FStar_Errors.Fatal_IllTyped, uu____7103) in
            FStar_Errors.raise_error uu____7098 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7105 =
              let uu____7110 =
                let uu____7111 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7111 in
              (FStar_Errors.Fatal_IllTyped, uu____7110) in
            FStar_Errors.raise_error uu____7105 r
        | FStar_Const.Const_reify  ->
            let uu____7112 =
              let uu____7117 =
                let uu____7118 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7118 in
              (FStar_Errors.Fatal_IllTyped, uu____7117) in
            FStar_Errors.raise_error uu____7112 r
        | FStar_Const.Const_reflect uu____7119 ->
            let uu____7120 =
              let uu____7125 =
                let uu____7126 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7126 in
              (FStar_Errors.Fatal_IllTyped, uu____7125) in
            FStar_Errors.raise_error uu____7120 r
        | uu____7127 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r
and tc_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.universe,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun c  ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____7144) ->
          let uu____7153 = FStar_Syntax_Util.type_u () in
          (match uu____7153 with
           | (k,u) ->
               let uu____7166 = tc_check_tot_or_gtot_term env t k in
               (match uu____7166 with
                | (t1,uu____7180,g) ->
                    let uu____7182 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7182, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7184) ->
          let uu____7193 = FStar_Syntax_Util.type_u () in
          (match uu____7193 with
           | (k,u) ->
               let uu____7206 = tc_check_tot_or_gtot_term env t k in
               (match uu____7206 with
                | (t1,uu____7220,g) ->
                    let uu____7222 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7222, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____7230 =
              let uu____7231 =
                let uu____7232 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____7232 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7231 in
            uu____7230 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____7235 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____7235 with
           | (tc1,uu____7249,f) ->
               let uu____7251 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____7251 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7295 =
                        let uu____7296 = FStar_Syntax_Subst.compress head3 in
                        uu____7296.FStar_Syntax_Syntax.n in
                      match uu____7295 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7299,us) -> us
                      | uu____7305 -> [] in
                    let uu____7306 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____7306 with
                     | (uu____7327,args1) ->
                         let uu____7349 =
                           let uu____7368 = FStar_List.hd args1 in
                           let uu____7381 = FStar_List.tl args1 in
                           (uu____7368, uu____7381) in
                         (match uu____7349 with
                          | (res,args2) ->
                              let uu____7446 =
                                let uu____7455 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___62_7483  ->
                                          match uu___62_7483 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7491 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7491 with
                                               | (env1,uu____7503) ->
                                                   let uu____7508 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7508 with
                                                    | (e1,uu____7520,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7455
                                  FStar_List.unzip in
                              (match uu____7446 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___84_7559 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___84_7559.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___84_7559.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7563 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7563 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7567 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7567))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7575 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7576 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7586 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7586
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7590 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7590
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7595 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7595 FStar_Pervasives_Native.snd
         | uu____7604 -> aux u)
and tc_abs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____7628 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____7628 top.FStar_Syntax_Syntax.pos in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7722 bs2 bs_expected1 =
              match uu____7722 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7890)) ->
                             let uu____7895 =
                               let uu____7900 =
                                 let uu____7901 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7901 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7900) in
                             let uu____7902 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____7895 uu____7902
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7903),FStar_Pervasives_Native.None ) ->
                             let uu____7908 =
                               let uu____7913 =
                                 let uu____7914 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7914 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7913) in
                             let uu____7915 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____7908 uu____7915
                         | uu____7916 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7922 =
                           let uu____7927 =
                             let uu____7928 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7928.FStar_Syntax_Syntax.n in
                           match uu____7927 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7935 ->
                               ((let uu____7937 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7937
                                 then
                                   let uu____7938 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7938
                                 else ());
                                (let uu____7940 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7940 with
                                 | (t,uu____7952,g1) ->
                                     let g2 =
                                       let uu____7955 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t in
                                       if uu____7955
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7957 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t in
                                          match uu____7957 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7960 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t in
                                              let uu____7965 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_Errors.raise_error
                                                uu____7960 uu____7965
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7967 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7967
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2) in
                                     let g3 =
                                       let uu____7969 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7969 in
                                     (t, g3))) in
                         match uu____7922 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___85_7997 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___85_7997.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___85_7997.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____8010 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____8010 in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         g, subst1)) in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____8158 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8167 = tc_binders env1 bs in
                  match uu____8167 with
                  | (bs1,envbody,g,uu____8197) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____8241 =
                    let uu____8242 = FStar_Syntax_Subst.compress t2 in
                    uu____8242.FStar_Syntax_Syntax.n in
                  match uu____8241 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8265 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8289 -> failwith "Impossible");
                       (let uu____8298 = tc_binders env1 bs in
                        match uu____8298 with
                        | (bs1,envbody,g,uu____8330) ->
                            let uu____8331 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8331 with
                             | (envbody1,uu____8359) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8370;
                         FStar_Syntax_Syntax.pos = uu____8371;
                         FStar_Syntax_Syntax.vars = uu____8372;_},uu____8373)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8417 -> failwith "Impossible");
                       (let uu____8426 = tc_binders env1 bs in
                        match uu____8426 with
                        | (bs1,envbody,g,uu____8458) ->
                            let uu____8459 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8459 with
                             | (envbody1,uu____8487) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8499) ->
                      let uu____8504 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8504 with
                       | (uu____8545,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8588 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8588 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8697 c_expected2 body3
                               =
                               match uu____8697 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8817 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8817, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8848 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8848 in
                                        let uu____8849 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8849, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8874 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8874
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env3
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____8926 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8926 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8949 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8949 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8999 =
                                                           let uu____9030 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9030,
                                                             subst2) in
                                                         handle_more
                                                           uu____8999
                                                           c_expected4 body3))
                                           | uu____9047 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None in
                                               (env3, bs2, guard, c, body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None in
                                           (env3, bs2, guard, c, body4))) in
                             let uu____9063 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____9063 c_expected1 body2 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___86_9120 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___86_9120.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___86_9120.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___86_9120.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___86_9120.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___86_9120.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___86_9120.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___86_9120.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___86_9120.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___86_9120.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___86_9120.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___86_9120.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___86_9120.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___86_9120.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___86_9120.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___86_9120.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___86_9120.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___86_9120.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___86_9120.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___86_9120.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___86_9120.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___86_9120.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___86_9120.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___86_9120.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___86_9120.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___86_9120.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___86_9120.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___86_9120.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___86_9120.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___86_9120.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___86_9120.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___86_9120.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___86_9120.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___86_9120.FStar_TypeChecker_Env.dep_graph)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9168  ->
                                     fun uu____9169  ->
                                       match (uu____9168, uu____9169) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9231 =
                                             let uu____9238 =
                                               let uu____9239 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____9239
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____9238 t3 in
                                           (match uu____9231 with
                                            | (t4,uu____9261,uu____9262) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9272 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___87_9275 =
                                                             x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___87_9275.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___87_9275.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____9272 ::
                                                        letrec_binders
                                                  | uu____9276 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____9281 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1 in
                           (match uu____9281 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9335 = mk_letrec_env envbody bs1 c in
                                (match uu____9335 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g))))
                  | uu____9381 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9402 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9402
                      else
                        (let uu____9404 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9404 with
                         | (uu____9443,bs1,uu____9445,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9465 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9465 with
          | (env1,topt) ->
              ((let uu____9485 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9485
                then
                  let uu____9486 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9486
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9490 = expected_function_typ1 env1 topt body in
                match uu____9490 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9530 =
                      let should_check_expected_effect =
                        let uu____9538 =
                          let uu____9545 =
                            let uu____9546 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9546.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9545) in
                        match uu____9538 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9551,(FStar_Util.Inr expected_c,uu____9553),uu____9554))
                            -> false
                        | uu____9603 -> true in
                      let uu____9610 =
                        tc_term
                          (let uu___88_9619 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___88_9619.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___88_9619.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___88_9619.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___88_9619.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___88_9619.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___88_9619.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___88_9619.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___88_9619.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___88_9619.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___88_9619.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___88_9619.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___88_9619.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___88_9619.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___88_9619.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___88_9619.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___88_9619.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___88_9619.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___88_9619.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___88_9619.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___88_9619.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___88_9619.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___88_9619.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___88_9619.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___88_9619.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___88_9619.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___88_9619.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___88_9619.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___88_9619.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___88_9619.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___88_9619.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___88_9619.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___88_9619.FStar_TypeChecker_Env.dep_graph)
                           }) body1 in
                      match uu____9610 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9636 =
                              let uu____9643 =
                                let uu____9648 =
                                  cbody.FStar_Syntax_Syntax.comp () in
                                (body2, uu____9648) in
                              check_expected_effect
                                (let uu___89_9655 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___89_9655.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___89_9655.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___89_9655.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___89_9655.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___89_9655.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___89_9655.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___89_9655.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___89_9655.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___89_9655.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___89_9655.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___89_9655.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___89_9655.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___89_9655.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___89_9655.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___89_9655.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___89_9655.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___89_9655.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___89_9655.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___89_9655.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___89_9655.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___89_9655.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___89_9655.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___89_9655.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___89_9655.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___89_9655.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___89_9655.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___89_9655.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___89_9655.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___89_9655.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___89_9655.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___89_9655.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___89_9655.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___89_9655.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9643 in
                            (match uu____9636 with
                             | (body3,cbody1,guard) ->
                                 let uu____9665 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9665))
                          else
                            (let uu____9667 =
                               cbody.FStar_Syntax_Syntax.comp () in
                             (body2, uu____9667, guard_body1)) in
                    (match uu____9530 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9682 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9684 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9684) in
                           if uu____9682
                           then
                             let uu____9685 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9685
                           else
                             (let guard1 =
                                let uu____9688 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9688 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9697 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9718 ->
                                    (e, t1, guard1)
                                | uu____9731 ->
                                    let uu____9732 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9732 with
                                     | (e1,guard') ->
                                         let uu____9745 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9745)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9697 with
                          | (e1,tfun,guard2) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun in
                              let uu____9758 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2 in
                              (match uu____9758 with
                               | (c1,g1) -> (e1, c1, g1))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = chead.FStar_Syntax_Syntax.res_typ in
              (let uu____9807 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9807
               then
                 let uu____9808 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9809 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9808
                   uu____9809
               else ());
              (let monadic_application uu____9866 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9866 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___90_9925 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___90_9925.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___90_9925.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___90_9925.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9926 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____9941 ->
                           let g =
                             let uu____9949 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9949
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9950 =
                             let uu____9951 =
                               let uu____9954 =
                                 let uu____9955 =
                                   let uu____9956 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____9956 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9955 in
                               FStar_Syntax_Syntax.mk_Total uu____9954 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9951 in
                           (uu____9950, g) in
                     (match uu____9926 with
                      | (cres2,guard1) ->
                          ((let uu____9970 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9970
                            then
                              let uu____9971 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9971
                            else ());
                           (let cres3 =
                              let head_or_some_arg_is_effectful =
                                (let uu____9977 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     chead1 in
                                 Prims.op_Negation uu____9977) ||
                                  (FStar_Util.for_some
                                     (fun uu____9990  ->
                                        match uu____9990 with
                                        | (uu____9999,uu____10000,lc) ->
                                            (let uu____10008 =
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 lc in
                                             Prims.op_Negation uu____10008)
                                              ||
                                              (FStar_TypeChecker_Util.should_not_inline_lc
                                                 lc)) arg_comps_rev) in
                              let uu____10009 =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   cres2)
                                  && head_or_some_arg_is_effectful in
                              if uu____10009
                              then
                                let term =
                                  FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets_rev)
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2 in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10043  ->
                                     match uu____10043 with
                                     | ((e,q),x,c) ->
                                         let uu____10076 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10076
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (FStar_Pervasives_Native.Some e)
                                             c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             FStar_Pervasives_Native.None c
                                             (x, out_c)) cres3 arg_comps_rev in
                            let comp1 =
                              let uu____10085 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  chead1 in
                              if uu____10085
                              then
                                FStar_TypeChecker_Util.bind
                                  head2.FStar_Syntax_Syntax.pos env
                                  (FStar_Pervasives_Native.Some head2) chead1
                                  (FStar_Pervasives_Native.None, comp)
                              else
                                FStar_TypeChecker_Util.bind
                                  head2.FStar_Syntax_Syntax.pos env
                                  FStar_Pervasives_Native.None chead1
                                  (FStar_Pervasives_Native.None, comp) in
                            let shortcuts_evaluation_order =
                              let uu____10092 =
                                let uu____10093 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____10093.FStar_Syntax_Syntax.n in
                              match uu____10092 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10097 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10118  ->
                                         match uu____10118 with
                                         | (arg,uu____10132,uu____10133) ->
                                             arg :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    FStar_Pervasives_Native.None r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____10143 =
                                   let map_fun uu____10205 =
                                     match uu____10205 with
                                     | ((e,q),uu____10240,c) ->
                                         let uu____10250 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10250
                                         then
                                           (FStar_Pervasives_Native.None,
                                             (e, q))
                                         else
                                           (let x =
                                              FStar_Syntax_Syntax.new_bv
                                                FStar_Pervasives_Native.None
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let e1 =
                                              FStar_TypeChecker_Util.maybe_lift
                                                env e
                                                c.FStar_Syntax_Syntax.eff_name
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let uu____10300 =
                                              let uu____10305 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____10305, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10300)) in
                                   let uu____10334 =
                                     let uu____10359 =
                                       let uu____10382 =
                                         let uu____10397 =
                                           let uu____10406 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10406,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____10397 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____10382 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10359 in
                                   match uu____10334 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10579 =
                                         let uu____10580 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10580 in
                                       let uu____10589 =
                                         let uu____10596 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10596 in
                                       (lifted_args, uu____10579,
                                         uu____10589) in
                                 match uu____10143 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___63_10699 =
                                       match uu___63_10699 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10754 =
                                               let uu____10757 =
                                                 let uu____10758 =
                                                   let uu____10771 =
                                                     let uu____10772 =
                                                       let uu____10773 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10773] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10772 e in
                                                   ((false, [lb]),
                                                     uu____10771) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10758 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10757 in
                                             uu____10754
                                               FStar_Pervasives_Native.None
                                               e.FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_meta
                                                (letbinding,
                                                  (FStar_Syntax_Syntax.Meta_monadic
                                                     (m,
                                                       (comp1.FStar_Syntax_Syntax.res_typ)))))
                                             FStar_Pervasives_Native.None
                                             e.FStar_Syntax_Syntax.pos in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____10803 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10803 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____10894 bs args1 =
                 match uu____10894 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11041))::rest,
                         (uu____11043,FStar_Pervasives_Native.None )::uu____11044)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____11105 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____11105 with
                           | (varg,uu____11125,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____11147 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____11147) in
                               let uu____11148 =
                                 let uu____11183 =
                                   let uu____11198 =
                                     let uu____11211 =
                                       let uu____11212 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____11212
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11211) in
                                   uu____11198 :: outargs in
                                 let uu____11231 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____11183, (arg :: arg_rets),
                                   uu____11231, fvs) in
                               tc_args head_info uu____11148 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11333),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11334)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11347 ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier")
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___91_11358 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___91_11358.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___91_11358.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____11360 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____11360
                             then
                               let uu____11361 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11361
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___92_11366 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___92_11366.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___92_11366.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___92_11366.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___92_11366.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___92_11366.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___92_11366.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___92_11366.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___92_11366.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___92_11366.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___92_11366.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___92_11366.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___92_11366.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___92_11366.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___92_11366.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___92_11366.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___92_11366.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___92_11366.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___92_11366.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___92_11366.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___92_11366.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___92_11366.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___92_11366.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___92_11366.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___92_11366.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___92_11366.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___92_11366.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___92_11366.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___92_11366.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___92_11366.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___92_11366.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___92_11366.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___92_11366.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___92_11366.FStar_TypeChecker_Env.dep_graph)
                               } in
                             (let uu____11368 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____11368
                              then
                                let uu____11369 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____11370 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11371 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11369 uu____11370 uu____11371
                              else ());
                             (let uu____11373 = tc_term env2 e in
                              match uu____11373 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____11408 =
                                      let uu____11411 =
                                        let uu____11418 =
                                          FStar_Syntax_Syntax.bv_to_name x1 in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11418 in
                                      FStar_Pervasives_Native.fst uu____11411 in
                                    (uu____11408, aq) in
                                  let uu____11425 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____11425
                                  then
                                    let subst2 =
                                      let uu____11433 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11433
                                        e1 in
                                    tc_args head_info
                                      (subst2,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, (x1 :: fvs)) rest
                                      rest'))))
                      | (uu____11559,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11595) ->
                          let uu____11646 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11646 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11680 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11680
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11705 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11705 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11728 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11728
                                            then
                                              FStar_Errors.log_issue
                                                tres1.FStar_Syntax_Syntax.pos
                                                (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                  "Potentially redundant explicit currying of a function type")
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11770 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2 in
                                       let uu____11776 =
                                         let uu____11777 =
                                           FStar_Syntax_Subst.compress tres3 in
                                         uu____11777.FStar_Syntax_Syntax.n in
                                       match uu____11776 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11780;
                                              FStar_Syntax_Syntax.index =
                                                uu____11781;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11783)
                                           -> norm_tres tres4
                                       | uu____11790 -> tres3 in
                                     let uu____11791 = norm_tres tres1 in
                                     aux true uu____11791
                                 | uu____11792 ->
                                     let uu____11793 =
                                       let uu____11798 =
                                         let uu____11799 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead in
                                         let uu____11800 =
                                           FStar_Util.string_of_int n_args in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____11799 uu____11800 in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____11798) in
                                     let uu____11807 =
                                       FStar_Syntax_Syntax.argpos arg in
                                     FStar_Errors.raise_error uu____11793
                                       uu____11807 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11826 =
                   let uu____11827 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11827.FStar_Syntax_Syntax.n in
                 match uu____11826 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11838 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11939 = tc_term env1 e in
                           (match uu____11939 with
                            | (e1,c,g_e) ->
                                let uu____11961 = tc_args1 env1 tl1 in
                                (match uu____11961 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12001 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12001))) in
                     let uu____12022 = tc_args1 env args in
                     (match uu____12022 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12059 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12097  ->
                                      match uu____12097 with
                                      | (uu____12110,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12059 in
                          let ml_or_tot t r1 =
                            let uu____12127 = FStar_Options.ml_ish () in
                            if uu____12127
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12130 =
                              let uu____12133 =
                                let uu____12134 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12134
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12133 in
                            ml_or_tot uu____12130 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12147 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12147
                            then
                              let uu____12148 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12149 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12150 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12148 uu____12149 uu____12150
                            else ());
                           (let uu____12153 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12153);
                           (let comp =
                              let uu____12155 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12166  ->
                                   fun out  ->
                                     match uu____12166 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12155 in
                            let uu____12180 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12183 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12180, comp, uu____12183))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____12186;
                        FStar_Syntax_Syntax.pos = uu____12187;
                        FStar_Syntax_Syntax.vars = uu____12188;_},uu____12189)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12310 = tc_term env1 e in
                           (match uu____12310 with
                            | (e1,c,g_e) ->
                                let uu____12332 = tc_args1 env1 tl1 in
                                (match uu____12332 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12372 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12372))) in
                     let uu____12393 = tc_args1 env args in
                     (match uu____12393 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12430 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12468  ->
                                      match uu____12468 with
                                      | (uu____12481,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12430 in
                          let ml_or_tot t r1 =
                            let uu____12498 = FStar_Options.ml_ish () in
                            if uu____12498
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12501 =
                              let uu____12504 =
                                let uu____12505 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12505
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12504 in
                            ml_or_tot uu____12501 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12518 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12518
                            then
                              let uu____12519 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12520 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12521 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12519 uu____12520 uu____12521
                            else ());
                           (let uu____12524 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12524);
                           (let comp =
                              let uu____12526 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12537  ->
                                   fun out  ->
                                     match uu____12537 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12526 in
                            let uu____12551 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12554 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12551, comp, uu____12554))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12575 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12575 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12640) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12646,uu____12647) -> check_function_app t
                 | uu____12688 ->
                     let uu____12689 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____12689
                       head1.FStar_Syntax_Syntax.pos in
               check_function_app thead)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____12763 =
                    FStar_List.fold_left2
                      (fun uu____12806  ->
                         fun uu____12807  ->
                           fun uu____12808  ->
                             match (uu____12806, uu____12807, uu____12808)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12876 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12876 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12894 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12894 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12898 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12898)
                                              &&
                                              (let uu____12900 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12900)) in
                                       let uu____12901 =
                                         let uu____12910 =
                                           let uu____12919 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12919] in
                                         FStar_List.append seen uu____12910 in
                                       let uu____12926 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12901, uu____12926, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12763 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12962 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12962
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12964 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12964 with | (c2,g) -> (e, c2, g)))
              | uu____12981 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Ident.lident,
          FStar_Syntax_Syntax.cflags Prims.list,Prims.bool ->
                                                  FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple6
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____13023 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____13023 with
        | (pattern,when_clause,branch_exp) ->
            let uu____13067 = branch1 in
            (match uu____13067 with
             | (cpat,uu____13107,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____13174 = FStar_Syntax_Util.type_u () in
                     match uu____13174 with
                     | (tu,u) ->
                         let uu____13185 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____13185 with
                          | (t1,uu____13197,g) -> (t1, g)) in
                   let uu____13199 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____13199 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____13233 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____13233
                         then
                           let uu____13234 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____13235 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____13234 uu____13235
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____13238 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____13238 with
                         | (env1,uu____13260) ->
                             let env11 =
                               let uu___93_13266 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___93_13266.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___93_13266.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___93_13266.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___93_13266.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___93_13266.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___93_13266.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___93_13266.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___93_13266.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___93_13266.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___93_13266.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___93_13266.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___93_13266.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___93_13266.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___93_13266.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___93_13266.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___93_13266.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___93_13266.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___93_13266.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___93_13266.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___93_13266.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___93_13266.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___93_13266.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___93_13266.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___93_13266.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___93_13266.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___93_13266.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___93_13266.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___93_13266.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___93_13266.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___93_13266.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___93_13266.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___93_13266.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___93_13266.FStar_TypeChecker_Env.dep_graph)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____13269 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____13269
                               then
                                 let uu____13270 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____13271 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____13270 uu____13271
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____13274 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____13274 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___94_13299 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___94_13299.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___94_13299.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___94_13299.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____13300 =
                                     let uu____13301 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____13301
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____13303 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____13303
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____13305 =
                                          let uu____13310 =
                                            let uu____13311 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ in
                                            let uu____13312 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____13311 uu____13312 in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____13310) in
                                        FStar_Errors.raise_error uu____13305
                                          exp1.FStar_Syntax_Syntax.pos) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____13329 =
                                       let uu____13330 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13330 in
                                     if uu____13329
                                     then
                                       let unresolved =
                                         let uu____13342 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____13342
                                           FStar_Util.set_elements in
                                       let uu____13369 =
                                         let uu____13374 =
                                           let uu____13375 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp in
                                           let uu____13376 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t in
                                           let uu____13377 =
                                             let uu____13378 =
                                               FStar_All.pipe_right
                                                 unresolved
                                                 (FStar_List.map
                                                    (fun uu____13396  ->
                                                       match uu____13396 with
                                                       | (u,uu____13402) ->
                                                           FStar_Syntax_Print.uvar_to_string
                                                             u)) in
                                             FStar_All.pipe_right uu____13378
                                               (FStar_String.concat ", ") in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____13375 uu____13376
                                             uu____13377 in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____13374) in
                                       FStar_Errors.raise_error uu____13369
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____13407 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____13407
                                     then
                                       let uu____13408 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13408
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1,
                                       guard_pat_annots, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____13417 =
                   let uu____13424 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____13424
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____13417 with
                  | (scrutinee_env,uu____13456) ->
                      let uu____13461 = tc_pat true pat_t pattern in
                      (match uu____13461 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13510 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13532 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____13532
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13546 =
                                      let uu____13553 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____13553 e in
                                    match uu____13546 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____13510 with
                            | (when_clause1,g_when) ->
                                let uu____13595 = tc_term pat_env branch_exp in
                                (match uu____13595 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Rel.conj_guard
                                         guard_pat_annots g_branch in
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13636 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13636 in
                                     let uu____13639 =
                                       let eqs =
                                         let uu____13657 =
                                           let uu____13658 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13658 in
                                         if uu____13657
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13665 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13682 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13683 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13684 ->
                                                let uu____13685 =
                                                  let uu____13686 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13686 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13685) in
                                       let uu____13687 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1 in
                                       match uu____13687 with
                                       | (c1,g_branch2) ->
                                           let uu____13710 =
                                             match (eqs, when_condition) with
                                             | uu____13723 when
                                                 let uu____13732 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13732
                                                 -> (c1, g_when)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.None
                                                ) -> (c1, g_when)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.None
                                                ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____13744 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13745 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13744, uu____13745)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13754 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13754 in
                                                 let uu____13755 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13756 =
                                                   let uu____13757 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13757 g_when in
                                                 (uu____13755, uu____13756)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13765 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13765, g_when) in
                                           (match uu____13710 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13790 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak) in
                                                    if uu____13790
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1 in
                                                let uu____13792 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13792, g_branch2)) in
                                     (match uu____13639 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13835 =
                                              let uu____13836 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13836 in
                                            if uu____13835
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13866 =
                                                     let uu____13867 =
                                                       let uu____13868 =
                                                         let uu____13871 =
                                                           let uu____13878 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13878 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13871 in
                                                       FStar_List.length
                                                         uu____13868 in
                                                     uu____13867 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13866
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13884 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13884 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13905 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13920 =
                                                             let uu____13921
                                                               =
                                                               let uu____13922
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13922] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13921 in
                                                           uu____13920
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13925 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13925]
                                                   else [] in
                                                 let fail uu____13930 =
                                                   let uu____13931 =
                                                     let uu____13932 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13933 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13934 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13932
                                                       uu____13933
                                                       uu____13934 in
                                                   failwith uu____13931 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13945) ->
                                                       head_constructor t1
                                                   | uu____13950 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13952 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13952
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13955 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13972;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13973;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13974;_},uu____13975)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____14012 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____14014 =
                                                       let uu____14015 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____14015
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____14014]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____14016 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14024 =
                                                       let uu____14025 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14025 in
                                                     if uu____14024
                                                     then []
                                                     else
                                                       (let uu____14029 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14029)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____14032 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14034 =
                                                       let uu____14035 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14035 in
                                                     if uu____14034
                                                     then []
                                                     else
                                                       (let uu____14039 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14039)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____14065 =
                                                       let uu____14066 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14066 in
                                                     if uu____14065
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____14073 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____14105
                                                                     ->
                                                                    match uu____14105
                                                                    with
                                                                    | 
                                                                    (ei,uu____14115)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____14121
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____14121
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____14142
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____14156
                                                                    =
                                                                    let uu____14157
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____14158
                                                                    =
                                                                    let uu____14159
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____14159] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____14157
                                                                    uu____14158 in
                                                                    uu____14156
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____14073
                                                            FStar_List.flatten in
                                                        let uu____14168 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____14168
                                                          sub_term_guards)
                                                 | uu____14171 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____14183 =
                                                   let uu____14184 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____14184 in
                                                 if uu____14183
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____14187 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____14187 in
                                                    let uu____14192 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____14192 with
                                                    | (k,uu____14198) ->
                                                        let uu____14199 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____14199
                                                         with
                                                         | (t1,uu____14207,uu____14208)
                                                             -> t1)) in
                                               let branch_guard =
                                                 build_and_check_branch_guard
                                                   scrutinee_tm norm_pat_exp in
                                               let branch_guard1 =
                                                 match when_condition with
                                                 | FStar_Pervasives_Native.None
                                                      -> branch_guard
                                                 | FStar_Pervasives_Native.Some
                                                     w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w in
                                               branch_guard1) in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch2 in
                                          ((let uu____14214 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____14214
                                            then
                                              let uu____14215 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____14215
                                            else ());
                                           (let uu____14217 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____14217, branch_guard,
                                              effect_label, cflags,
                                              maybe_return_c, guard)))))))))
and check_top_level_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____14247 = check_let_bound_def true env1 lb in
          (match uu____14247 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____14269 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14286 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____14286, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____14289 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____14289
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____14293 =
                      let uu____14306 =
                        let uu____14321 =
                          let uu____14330 =
                            let uu____14343 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14343) in
                          [uu____14330] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____14321 in
                      FStar_List.hd uu____14306 in
                    match uu____14293 with
                    | (uu____14396,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Rel.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.NoDeltaSteps;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1) in
                        let g13 =
                          FStar_TypeChecker_Rel.abstract_guard_n gvs g12 in
                        (g13, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____14269 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14419 =
                      let uu____14426 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____14426
                      then
                        let uu____14433 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____14433 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14456 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____14456
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14457 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____14457, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14467 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____14467
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____14475 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____14475
                            then e2
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                FStar_Pervasives_Native.None
                                e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____14419 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit in
                         let lb1 =
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             (FStar_Syntax_Util.comp_result c12)
                             (FStar_Syntax_Util.comp_effect_name c12) e11 in
                         let uu____14499 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____14499,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14514 -> failwith "Impossible"
and check_inner_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___95_14545 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___95_14545.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___95_14545.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___95_14545.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___95_14545.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___95_14545.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___95_14545.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___95_14545.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___95_14545.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___95_14545.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___95_14545.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___95_14545.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___95_14545.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___95_14545.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___95_14545.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___95_14545.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___95_14545.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___95_14545.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___95_14545.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___95_14545.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___95_14545.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___95_14545.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___95_14545.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___95_14545.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___95_14545.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___95_14545.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___95_14545.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___95_14545.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___95_14545.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___95_14545.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___95_14545.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___95_14545.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___95_14545.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___95_14545.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____14546 =
            let uu____14557 =
              let uu____14558 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____14558 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____14557 lb in
          (match uu____14546 with
           | (e1,uu____14580,c1,g1,annotated) ->
               let x =
                 let uu___96_14585 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___96_14585.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___96_14585.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____14586 =
                 let uu____14591 =
                   let uu____14592 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____14592] in
                 FStar_Syntax_Subst.open_term uu____14591 e2 in
               (match uu____14586 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                    let uu____14612 = tc_term env_x e21 in
                    (match uu____14612 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.maybe_return_e2_and_bind
                             e1.FStar_Syntax_Syntax.pos env2
                             (FStar_Pervasives_Native.Some e1) c1 e22
                             ((FStar_Pervasives_Native.Some x1), c2) in
                         let e11 =
                           FStar_TypeChecker_Util.maybe_lift env2 e1
                             c1.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c1.FStar_Syntax_Syntax.res_typ in
                         let e23 =
                           FStar_TypeChecker_Util.maybe_lift env2 e22
                             c2.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.eff_name
                             c2.FStar_Syntax_Syntax.res_typ in
                         let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             (FStar_Util.Inl x1) []
                             c1.FStar_Syntax_Syntax.res_typ
                             c1.FStar_Syntax_Syntax.eff_name e11 in
                         let e3 =
                           let uu____14637 =
                             let uu____14640 =
                               let uu____14641 =
                                 let uu____14654 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14654) in
                               FStar_Syntax_Syntax.Tm_let uu____14641 in
                             FStar_Syntax_Syntax.mk uu____14640 in
                           uu____14637 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14668 =
                             let uu____14669 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14670 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14669
                               c1.FStar_Syntax_Syntax.res_typ uu____14670 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14668 in
                         let g21 =
                           let uu____14672 =
                             let uu____14673 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14673 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14672 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14675 =
                           let uu____14676 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14676 in
                         if uu____14675
                         then
                           let tt =
                             let uu____14686 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14686
                               FStar_Option.get in
                           ((let uu____14692 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14692
                             then
                               let uu____14693 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14694 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14693 uu____14694
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14699 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14699
                             then
                               let uu____14700 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14701 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14700 uu____14701
                             else ());
                            (e4,
                              ((let uu___97_14704 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___97_14704.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___97_14704.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___97_14704.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14705 -> failwith "Impossible"
and check_top_level_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____14737 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14737 with
           | (lbs1,e21) ->
               let uu____14756 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14756 with
                | (env0,topt) ->
                    let uu____14775 = build_let_rec_env true env0 lbs1 in
                    (match uu____14775 with
                     | (lbs2,rec_env) ->
                         let uu____14794 = check_let_recs rec_env lbs2 in
                         (match uu____14794 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14814 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14814
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14820 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14820
                                  (fun _0_43  ->
                                     FStar_Pervasives_Native.Some _0_43) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef))
                                else
                                  (let ecs =
                                     let uu____14869 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14909 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14909))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14869 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14958  ->
                                           match uu____14958 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____15005 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____15005 in
                              let uu____15010 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____15010 with
                               | (lbs5,e22) ->
                                   ((let uu____15030 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____15030
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____15031 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____15031, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____15044 -> failwith "Impossible"
and check_inner_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____15076 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____15076 with
           | (lbs1,e21) ->
               let uu____15095 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____15095 with
                | (env0,topt) ->
                    let uu____15114 = build_let_rec_env false env0 lbs1 in
                    (match uu____15114 with
                     | (lbs2,rec_env) ->
                         let uu____15133 = check_let_recs rec_env lbs2 in
                         (match uu____15133 with
                          | (lbs3,g_lbs) ->
                              let uu____15152 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___98_15175 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___98_15175.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___98_15175.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___99_15177 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___99_15177.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___99_15177.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___99_15177.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___99_15177.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____15152 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____15204 = tc_term env2 e21 in
                                   (match uu____15204 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres in
                                        let cres2 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres1
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____15223 =
                                            let uu____15224 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____15224 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____15223 in
                                        let cres3 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres2 in
                                        let tres =
                                          norm env2
                                            cres3.FStar_Syntax_Syntax.res_typ in
                                        let cres4 =
                                          let uu___100_15228 = cres3 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___100_15228.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___100_15228.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___100_15228.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____15229 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____15229 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____15265 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres5 =
                                                    let uu___101_15270 =
                                                      cres4 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___101_15270.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___101_15270.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___101_15270.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres5, guard)))))))))
      | uu____15273 -> failwith "Impossible"
and build_let_rec_env:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____15302 = FStar_Options.ml_ish () in
          if uu____15302
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____15305 = FStar_Syntax_Util.arrow_formals_comp t in
             match uu____15305 with
             | (formals,c) ->
                 let uu____15330 = FStar_Syntax_Util.abs_formals lbdef in
                 (match uu____15330 with
                  | (actuals,uu____15340,uu____15341) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____15354 =
                          let uu____15359 =
                            let uu____15360 =
                              FStar_Syntax_Print.term_to_string lbdef in
                            let uu____15361 =
                              FStar_Syntax_Print.term_to_string lbtyp in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____15360 uu____15361 in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____15359) in
                        FStar_Errors.raise_error uu____15354
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____15364 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____15364 actuals in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1 in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____15385 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____15385) in
                            let formals_msg =
                              let n1 = FStar_List.length formals in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____15403 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments"
                                   uu____15403) in
                            let msg =
                              let uu____15411 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              let uu____15412 =
                                FStar_Syntax_Print.lbname_to_string lbname in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____15411 uu____15412 formals_msg
                                actuals_msg in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c) in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect))))) in
        let uu____15419 =
          FStar_List.fold_left
            (fun uu____15445  ->
               fun lb  ->
                 match uu____15445 with
                 | (lbs1,env1) ->
                     let uu____15465 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____15465 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1 in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let t1 =
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let uu____15485 =
                                 let uu____15492 =
                                   let uu____15493 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15493 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___102_15504 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___102_15504.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___102_15504.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___102_15504.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___102_15504.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___102_15504.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___102_15504.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___102_15504.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___102_15504.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___102_15504.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___102_15504.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___102_15504.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___102_15504.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___102_15504.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___102_15504.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___102_15504.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___102_15504.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___102_15504.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___102_15504.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___102_15504.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___102_15504.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___102_15504.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___102_15504.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___102_15504.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___102_15504.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___102_15504.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___102_15504.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___102_15504.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___102_15504.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___102_15504.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___102_15504.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___102_15504.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___102_15504.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___102_15504.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15492 in
                               match uu____15485 with
                               | (t1,uu____15506,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____15510 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15510);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____15512 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1 in
                            if uu____15512
                            then
                              let uu___103_15513 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___103_15513.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___103_15513.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___103_15513.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___103_15513.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___103_15513.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___103_15513.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___103_15513.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___103_15513.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___103_15513.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___103_15513.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___103_15513.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___103_15513.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___103_15513.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___103_15513.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___103_15513.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___103_15513.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___103_15513.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___103_15513.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___103_15513.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___103_15513.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___103_15513.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___103_15513.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___103_15513.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___103_15513.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___103_15513.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___103_15513.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___103_15513.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___103_15513.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___103_15513.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___103_15513.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___103_15513.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___103_15513.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___103_15513.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1) in
                          let lb1 =
                            let uu___104_15530 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___104_15530.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___104_15530.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____15419 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15553 =
        let uu____15562 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15588 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____15588 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15616 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15616
                       | uu____15621 ->
                           let lb1 =
                             let uu___105_15624 = lb in
                             let uu____15625 =
                               FStar_Syntax_Util.abs bs t lcomp in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___105_15624.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___105_15624.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___105_15624.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___105_15624.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15625
                             } in
                           let uu____15628 =
                             let uu____15635 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp in
                             tc_tot_or_gtot_term uu____15635
                               lb1.FStar_Syntax_Syntax.lbdef in
                           (match uu____15628 with
                            | (e,c,g) ->
                                ((let uu____15644 =
                                    let uu____15645 =
                                      FStar_Syntax_Util.is_total_lcomp c in
                                    Prims.op_Negation uu____15645 in
                                  if uu____15644
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let lb2 =
                                    FStar_Syntax_Util.mk_letbinding
                                      lb1.FStar_Syntax_Syntax.lbname
                                      lb1.FStar_Syntax_Syntax.lbunivs
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                      FStar_Parser_Const.effect_Tot_lid e in
                                  (lb2, g))))))) in
        FStar_All.pipe_right uu____15562 FStar_List.unzip in
      match uu____15553 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard in
          (lbs1, g_lbs)
and check_let_bound_def:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t,Prims.bool)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____15694 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15694 with
        | (env1,uu____15712) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15720 = check_lbtyp top_level env lb in
            (match uu____15720 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15764 =
                     tc_maybe_toplevel_term
                       (let uu___106_15773 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___106_15773.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___106_15773.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___106_15773.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___106_15773.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___106_15773.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___106_15773.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___106_15773.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___106_15773.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___106_15773.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___106_15773.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___106_15773.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___106_15773.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___106_15773.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___106_15773.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___106_15773.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___106_15773.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___106_15773.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___106_15773.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___106_15773.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___106_15773.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___106_15773.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___106_15773.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___106_15773.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___106_15773.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___106_15773.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___106_15773.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___106_15773.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___106_15773.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___106_15773.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___106_15773.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___106_15773.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___106_15773.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___106_15773.FStar_TypeChecker_Env.dep_graph)
                        }) e11 in
                   match uu____15764 with
                   | (e12,c1,g1) ->
                       let uu____15787 =
                         let uu____15792 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15796  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15792 e12 c1 wf_annot in
                       (match uu____15787 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15811 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15811
                              then
                                let uu____15812 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15813 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____15814 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15812 uu____15813 uu____15814
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and check_lbtyp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.subst_elt
                                           Prims.list,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____15848 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15848 with
             | (univ_opening,univ_vars1) ->
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, env))
        | uu____15887 ->
            let uu____15888 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15888 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15937 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15937)
                 else
                   (let uu____15945 = FStar_Syntax_Util.type_u () in
                    match uu____15945 with
                    | (k,uu____15965) ->
                        let uu____15966 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15966 with
                         | (t2,uu____15988,g) ->
                             ((let uu____15991 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15991
                               then
                                 let uu____15992 =
                                   let uu____15993 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15993 in
                                 let uu____15994 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15992 uu____15994
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15997 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15997))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____16005  ->
      match uu____16005 with
      | (x,imp) ->
          let uu____16024 = FStar_Syntax_Util.type_u () in
          (match uu____16024 with
           | (tu,u) ->
               ((let uu____16044 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____16044
                 then
                   let uu____16045 = FStar_Syntax_Print.bv_to_string x in
                   let uu____16046 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____16047 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____16045 uu____16046 uu____16047
                 else ());
                (let uu____16049 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____16049 with
                 | (t,uu____16069,g) ->
                     let x1 =
                       ((let uu___107_16077 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___107_16077.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___107_16077.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____16079 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____16079
                       then
                         let uu____16080 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____16081 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____16080 uu____16081
                       else ());
                      (let uu____16083 = push_binding env x1 in
                       (x1, uu____16083, g, u))))))
and tc_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____16173 = tc_binder env1 b in
            (match uu____16173 with
             | (b1,env',g,u) ->
                 let uu____16214 = aux env' bs2 in
                 (match uu____16214 with
                  | (bs3,env'1,g',us) ->
                      let uu____16267 =
                        let uu____16268 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____16268 in
                      ((b1 :: bs3), env'1, uu____16267, (u :: us)))) in
      aux env bs
and tc_pats:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____16353  ->
             fun uu____16354  ->
               match (uu____16353, uu____16354) with
               | ((t,imp),(args1,g)) ->
                   let uu____16423 = tc_term env1 t in
                   (match uu____16423 with
                    | (t1,uu____16441,g') ->
                        let uu____16443 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____16443))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16485  ->
             match uu____16485 with
             | (pats1,g) ->
                 let uu____16510 = tc_args env p in
                 (match uu____16510 with
                  | (args,g') ->
                      let uu____16523 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____16523))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____16536 = tc_maybe_toplevel_term env e in
      match uu____16536 with
      | (e1,c,g) ->
          let uu____16552 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____16552
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____16565 =
               let uu____16570 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____16570
               then
                 let uu____16575 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____16575, false)
               else
                 (let uu____16577 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____16577, true)) in
             match uu____16565 with
             | (target_comp,allow_ghost) ->
                 let uu____16586 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____16586 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16596 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____16596)
                  | uu____16597 ->
                      if allow_ghost
                      then
                        let uu____16606 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2 in
                        FStar_Errors.raise_error uu____16606
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16618 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2 in
                         FStar_Errors.raise_error uu____16618
                           e1.FStar_Syntax_Syntax.pos)))
and tc_check_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and tc_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____16641 = tc_tot_or_gtot_term env t in
      match uu____16641 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let type_of_tot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      (let uu____16669 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16669
       then
         let uu____16670 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16670
       else ());
      (let env1 =
         let uu___108_16673 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___108_16673.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___108_16673.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___108_16673.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___108_16673.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___108_16673.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___108_16673.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___108_16673.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___108_16673.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___108_16673.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___108_16673.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___108_16673.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___108_16673.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___108_16673.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___108_16673.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___108_16673.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___108_16673.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___108_16673.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___108_16673.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___108_16673.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___108_16673.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___108_16673.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___108_16673.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___108_16673.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___108_16673.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___108_16673.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___108_16673.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___108_16673.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___108_16673.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___108_16673.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___108_16673.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___108_16673.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___108_16673.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____16680 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16715) ->
             let uu____16716 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____16716 in
       match uu____16680 with
       | (t,c,g) ->
           let uu____16732 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16732
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16742 =
                let uu____16747 =
                  let uu____16748 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16748 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16747) in
              let uu____16749 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____16742 uu____16749))
let level_of_type_fail:
  'Auu____16760 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16760
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16773 =
          let uu____16778 =
            let uu____16779 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16779 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16778) in
        let uu____16780 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____16773 uu____16780
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16797 =
            let uu____16798 = FStar_Syntax_Util.unrefine t1 in
            uu____16798.FStar_Syntax_Syntax.n in
          match uu____16797 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16802 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16805 = FStar_Syntax_Util.type_u () in
                 match uu____16805 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___111_16813 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___111_16813.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___111_16813.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___111_16813.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___111_16813.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___111_16813.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___111_16813.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___111_16813.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___111_16813.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___111_16813.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___111_16813.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___111_16813.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___111_16813.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___111_16813.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___111_16813.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___111_16813.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___111_16813.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___111_16813.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___111_16813.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___111_16813.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___111_16813.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___111_16813.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___111_16813.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___111_16813.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___111_16813.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___111_16813.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___111_16813.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___111_16813.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___111_16813.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___111_16813.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___111_16813.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___111_16813.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___111_16813.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___111_16813.FStar_TypeChecker_Env.dep_graph)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16817 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16817
                       | uu____16818 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec universe_of_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____16827 =
        let uu____16828 = FStar_Syntax_Subst.compress e in
        uu____16828.FStar_Syntax_Syntax.n in
      match uu____16827 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16833 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16838 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16865 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16881) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16904,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16931) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16938 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16938 with | ((uu____16949,t),uu____16951) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16956,(FStar_Util.Inl t,uu____16958),uu____16959) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____17006,(FStar_Util.Inr c,uu____17008),uu____17009) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____17059;
             FStar_Syntax_Syntax.vars = uu____17060;_},us)
          ->
          let uu____17066 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____17066 with
           | ((us',t),uu____17079) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____17085 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____17085)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____17101 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____17102 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____17112) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____17135 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____17135 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____17155  ->
                      match uu____17155 with
                      | (b,uu____17161) ->
                          let uu____17162 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____17162) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____17167 = universe_of_aux env res in
                 level_of_type env res uu____17167 in
               let u_c =
                 let uu____17169 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____17169 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____17173 = universe_of_aux env trepr in
                     level_of_type env trepr uu____17173 in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____17266 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____17281 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____17320 ->
                let uu____17321 = universe_of_aux env hd3 in
                (uu____17321, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17334 ->
                let uu____17335 = universe_of_aux env hd3 in
                (uu____17335, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17348 ->
                let uu____17365 = universe_of_aux env hd3 in
                (uu____17365, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17378 ->
                let uu____17385 = universe_of_aux env hd3 in
                (uu____17385, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17398 ->
                let uu____17425 = universe_of_aux env hd3 in
                (uu____17425, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17438 ->
                let uu____17445 = universe_of_aux env hd3 in
                (uu____17445, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17458 ->
                let uu____17459 = universe_of_aux env hd3 in
                (uu____17459, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17472 ->
                let uu____17485 = universe_of_aux env hd3 in
                (uu____17485, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17498 ->
                let uu____17505 = universe_of_aux env hd3 in
                (uu____17505, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17518 ->
                let uu____17519 = universe_of_aux env hd3 in
                (uu____17519, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17532,hd4::uu____17534) ->
                let uu____17599 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____17599 with
                 | (uu____17614,uu____17615,hd5) ->
                     let uu____17633 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____17633 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17684 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17686 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17686 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17737 ->
                let uu____17738 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17738 with
                 | (env1,uu____17760) ->
                     let env2 =
                       let uu___112_17766 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_17766.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_17766.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_17766.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_17766.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_17766.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_17766.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_17766.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_17766.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_17766.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_17766.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_17766.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___112_17766.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_17766.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_17766.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_17766.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_17766.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_17766.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_17766.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___112_17766.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___112_17766.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___112_17766.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_17766.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_17766.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___112_17766.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___112_17766.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___112_17766.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___112_17766.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___112_17766.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___112_17766.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___112_17766.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___112_17766.FStar_TypeChecker_Env.dep_graph)
                       } in
                     ((let uu____17768 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17768
                       then
                         let uu____17769 =
                           let uu____17770 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17770 in
                         let uu____17771 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17769 uu____17771
                       else ());
                      (let uu____17773 = tc_term env2 hd3 in
                       match uu____17773 with
                       | (uu____17794,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17795;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17797;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17798;_},g)
                           ->
                           ((let uu____17809 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17809
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17820 = type_of_head true hd1 args in
          (match uu____17820 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17860 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17860 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17904 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17904)))
      | FStar_Syntax_Syntax.Tm_match (uu____17907,hd1::uu____17909) ->
          let uu____17974 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17974 with
           | (uu____17977,uu____17978,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17996,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____18039 = universe_of_aux env e in
      level_of_type env e uu____18039
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____18058 = tc_binders env tps in
      match uu____18058 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))