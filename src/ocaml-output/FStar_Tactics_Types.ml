open Prims
type goal =
  {
  goal_main_env: FStar_TypeChecker_Env.env ;
  goal_ctx_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  opts: FStar_Options.optionstate ;
  is_guard: Prims.bool }
let (__proj__Mkgoal__item__goal_main_env : goal -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_main_env
  
let (__proj__Mkgoal__item__goal_ctx_uvar :
  goal -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__goal_ctx_uvar
  
let (__proj__Mkgoal__item__opts : goal -> FStar_Options.optionstate) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__opts
  
let (__proj__Mkgoal__item__is_guard : goal -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { goal_main_env = __fname__goal_main_env;
        goal_ctx_uvar = __fname__goal_ctx_uvar; opts = __fname__opts;
        is_guard = __fname__is_guard;_} -> __fname__is_guard
  
let (goal_env : goal -> FStar_TypeChecker_Env.env) =
  fun g  ->
    let uu___238_62 = g.goal_main_env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___238_62.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___238_62.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___238_62.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma =
        ((g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___238_62.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___238_62.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___238_62.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___238_62.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___238_62.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___238_62.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp =
        (uu___238_62.FStar_TypeChecker_Env.instantiate_imp);
      FStar_TypeChecker_Env.effects =
        (uu___238_62.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___238_62.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___238_62.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___238_62.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___238_62.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___238_62.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___238_62.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___238_62.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___238_62.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___238_62.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___238_62.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___238_62.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___238_62.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___238_62.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___238_62.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___238_62.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___238_62.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___238_62.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___238_62.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___238_62.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___238_62.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___238_62.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___238_62.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___238_62.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___238_62.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___238_62.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___238_62.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___238_62.FStar_TypeChecker_Env.dep_graph)
    }
  
let (goal_witness : goal -> FStar_Syntax_Syntax.term) =
  fun g  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uvar
         ((g.goal_ctx_uvar), ([], FStar_Syntax_Syntax.NoUseRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (goal_type : goal -> FStar_Syntax_Syntax.term) =
  fun g  -> (g.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ 
let (goal_with_type : goal -> FStar_Syntax_Syntax.term -> goal) =
  fun g  ->
    fun t  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___239_99 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = t;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___239_99.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___240_100 = g  in
      {
        goal_main_env = (uu___240_100.goal_main_env);
        goal_ctx_uvar = c';
        opts = (uu___240_100.opts);
        is_guard = (uu___240_100.is_guard)
      }
  
let (goal_with_env : goal -> FStar_TypeChecker_Env.env -> goal) =
  fun g  ->
    fun env  ->
      let c = g.goal_ctx_uvar  in
      let c' =
        let uu___241_113 = c  in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma =
            (env.FStar_TypeChecker_Env.gamma);
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_typ);
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___241_113.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___242_114 = g  in
      {
        goal_main_env = env;
        goal_ctx_uvar = c';
        opts = (uu___242_114.opts);
        is_guard = (uu___242_114.is_guard)
      }
  
let (mk_goal :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Options.optionstate -> Prims.bool -> goal)
  =
  fun env  ->
    fun u  ->
      fun o  ->
        fun b  ->
          { goal_main_env = env; goal_ctx_uvar = u; opts = o; is_guard = b }
  
let (subst_goal : FStar_Syntax_Syntax.subst_elt Prims.list -> goal -> goal) =
  fun subst1  ->
    fun goal  ->
      let g = goal.goal_ctx_uvar  in
      let ctx_uvar =
        let uu___243_151 = g  in
        let uu____152 =
          FStar_TypeChecker_Env.rename_gamma subst1
            g.FStar_Syntax_Syntax.ctx_uvar_gamma
           in
        let uu____155 =
          FStar_Syntax_Subst.subst subst1 g.FStar_Syntax_Syntax.ctx_uvar_typ
           in
        {
          FStar_Syntax_Syntax.ctx_uvar_head =
            (uu___243_151.FStar_Syntax_Syntax.ctx_uvar_head);
          FStar_Syntax_Syntax.ctx_uvar_gamma = uu____152;
          FStar_Syntax_Syntax.ctx_uvar_binders =
            (uu___243_151.FStar_Syntax_Syntax.ctx_uvar_binders);
          FStar_Syntax_Syntax.ctx_uvar_typ = uu____155;
          FStar_Syntax_Syntax.ctx_uvar_reason =
            (uu___243_151.FStar_Syntax_Syntax.ctx_uvar_reason);
          FStar_Syntax_Syntax.ctx_uvar_should_check =
            (uu___243_151.FStar_Syntax_Syntax.ctx_uvar_should_check);
          FStar_Syntax_Syntax.ctx_uvar_range =
            (uu___243_151.FStar_Syntax_Syntax.ctx_uvar_range)
        }  in
      let uu___244_158 = goal  in
      {
        goal_main_env = (uu___244_158.goal_main_env);
        goal_ctx_uvar = ctx_uvar;
        opts = (uu___244_158.opts);
        is_guard = (uu___244_158.is_guard)
      }
  
type guard_policy =
  | Goal 
  | SMT 
  | Force 
  | Drop 
let (uu___is_Goal : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Goal  -> true | uu____164 -> false 
let (uu___is_SMT : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | SMT  -> true | uu____170 -> false 
let (uu___is_Force : guard_policy -> Prims.bool) =
  fun projectee  ->
    match projectee with | Force  -> true | uu____176 -> false
  
let (uu___is_Drop : guard_policy -> Prims.bool) =
  fun projectee  -> match projectee with | Drop  -> true | uu____182 -> false 
type proofstate =
  {
  main_context: FStar_TypeChecker_Env.env ;
  main_goal: goal ;
  all_implicits: FStar_TypeChecker_Env.implicits ;
  goals: goal Prims.list ;
  smt_goals: goal Prims.list ;
  depth: Prims.int ;
  __dump: proofstate -> Prims.string -> unit ;
  psc: FStar_TypeChecker_Normalize.psc ;
  entry_range: FStar_Range.range ;
  guard_policy: guard_policy ;
  freshness: Prims.int ;
  tac_verb_dbg: Prims.bool }
let (__proj__Mkproofstate__item__main_context :
  proofstate -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__main_context
  
let (__proj__Mkproofstate__item__main_goal : proofstate -> goal) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__main_goal
  
let (__proj__Mkproofstate__item__all_implicits :
  proofstate -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__all_implicits
  
let (__proj__Mkproofstate__item__goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__goals
  
let (__proj__Mkproofstate__item__smt_goals : proofstate -> goal Prims.list) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__smt_goals
  
let (__proj__Mkproofstate__item__depth : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__depth
  
let (__proj__Mkproofstate__item____dump :
  proofstate -> proofstate -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname____dump
  
let (__proj__Mkproofstate__item__psc :
  proofstate -> FStar_TypeChecker_Normalize.psc) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__psc
  
let (__proj__Mkproofstate__item__entry_range :
  proofstate -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__entry_range
  
let (__proj__Mkproofstate__item__guard_policy : proofstate -> guard_policy) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__guard_policy
  
let (__proj__Mkproofstate__item__freshness : proofstate -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__freshness
  
let (__proj__Mkproofstate__item__tac_verb_dbg : proofstate -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { main_context = __fname__main_context; main_goal = __fname__main_goal;
        all_implicits = __fname__all_implicits; goals = __fname__goals;
        smt_goals = __fname__smt_goals; depth = __fname__depth;
        __dump = __fname____dump; psc = __fname__psc;
        entry_range = __fname__entry_range;
        guard_policy = __fname__guard_policy; freshness = __fname__freshness;
        tac_verb_dbg = __fname__tac_verb_dbg;_} -> __fname__tac_verb_dbg
  
let (subst_proof_state :
  FStar_Syntax_Syntax.subst_t -> proofstate -> proofstate) =
  fun subst1  ->
    fun ps  ->
      let uu____613 = FStar_Options.tactic_raw_binders ()  in
      if uu____613
      then ps
      else
        (let uu___245_615 = ps  in
         let uu____616 = subst_goal subst1 ps.main_goal  in
         let uu____617 = FStar_List.map (subst_goal subst1) ps.goals  in
         {
           main_context = (uu___245_615.main_context);
           main_goal = uu____616;
           all_implicits = (uu___245_615.all_implicits);
           goals = uu____617;
           smt_goals = (uu___245_615.smt_goals);
           depth = (uu___245_615.depth);
           __dump = (uu___245_615.__dump);
           psc = (uu___245_615.psc);
           entry_range = (uu___245_615.entry_range);
           guard_policy = (uu___245_615.guard_policy);
           freshness = (uu___245_615.freshness);
           tac_verb_dbg = (uu___245_615.tac_verb_dbg)
         })
  
let (decr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___246_625 = ps  in
    {
      main_context = (uu___246_625.main_context);
      main_goal = (uu___246_625.main_goal);
      all_implicits = (uu___246_625.all_implicits);
      goals = (uu___246_625.goals);
      smt_goals = (uu___246_625.smt_goals);
      depth = (ps.depth - (Prims.parse_int "1"));
      __dump = (uu___246_625.__dump);
      psc = (uu___246_625.psc);
      entry_range = (uu___246_625.entry_range);
      guard_policy = (uu___246_625.guard_policy);
      freshness = (uu___246_625.freshness);
      tac_verb_dbg = (uu___246_625.tac_verb_dbg)
    }
  
let (incr_depth : proofstate -> proofstate) =
  fun ps  ->
    let uu___247_631 = ps  in
    {
      main_context = (uu___247_631.main_context);
      main_goal = (uu___247_631.main_goal);
      all_implicits = (uu___247_631.all_implicits);
      goals = (uu___247_631.goals);
      smt_goals = (uu___247_631.smt_goals);
      depth = (ps.depth + (Prims.parse_int "1"));
      __dump = (uu___247_631.__dump);
      psc = (uu___247_631.psc);
      entry_range = (uu___247_631.entry_range);
      guard_policy = (uu___247_631.guard_policy);
      freshness = (uu___247_631.freshness);
      tac_verb_dbg = (uu___247_631.tac_verb_dbg)
    }
  
let (tracepoint : proofstate -> unit) =
  fun ps  ->
    let uu____637 =
      (FStar_Options.tactic_trace ()) ||
        (let uu____639 = FStar_Options.tactic_trace_d ()  in
         ps.depth <= uu____639)
       in
    if uu____637
    then
      let uu____640 =
        let uu____641 = FStar_TypeChecker_Normalize.psc_subst ps.psc  in
        subst_proof_state uu____641 ps  in
      ps.__dump uu____640 "TRACE"
    else ()
  
let (set_ps_psc :
  FStar_TypeChecker_Normalize.psc -> proofstate -> proofstate) =
  fun psc  ->
    fun ps  ->
      let uu___248_653 = ps  in
      {
        main_context = (uu___248_653.main_context);
        main_goal = (uu___248_653.main_goal);
        all_implicits = (uu___248_653.all_implicits);
        goals = (uu___248_653.goals);
        smt_goals = (uu___248_653.smt_goals);
        depth = (uu___248_653.depth);
        __dump = (uu___248_653.__dump);
        psc;
        entry_range = (uu___248_653.entry_range);
        guard_policy = (uu___248_653.guard_policy);
        freshness = (uu___248_653.freshness);
        tac_verb_dbg = (uu___248_653.tac_verb_dbg)
      }
  
let (set_proofstate_range : proofstate -> FStar_Range.range -> proofstate) =
  fun ps  ->
    fun r  ->
      let uu___249_664 = ps  in
      let uu____665 =
        let uu____666 = FStar_Range.def_range r  in
        FStar_Range.set_def_range ps.entry_range uu____666  in
      {
        main_context = (uu___249_664.main_context);
        main_goal = (uu___249_664.main_goal);
        all_implicits = (uu___249_664.all_implicits);
        goals = (uu___249_664.goals);
        smt_goals = (uu___249_664.smt_goals);
        depth = (uu___249_664.depth);
        __dump = (uu___249_664.__dump);
        psc = (uu___249_664.psc);
        entry_range = uu____665;
        guard_policy = (uu___249_664.guard_policy);
        freshness = (uu___249_664.freshness);
        tac_verb_dbg = (uu___249_664.tac_verb_dbg)
      }
  
type direction =
  | TopDown 
  | BottomUp 
let (uu___is_TopDown : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopDown  -> true | uu____672 -> false
  
let (uu___is_BottomUp : direction -> Prims.bool) =
  fun projectee  ->
    match projectee with | BottomUp  -> true | uu____678 -> false
  