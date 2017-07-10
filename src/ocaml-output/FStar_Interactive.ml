open Prims
let tc_one_file:
  Prims.string Prims.list ->
    FStar_Universal.uenv ->
      ((Prims.string FStar_Pervasives_Native.option,Prims.string)
         FStar_Pervasives_Native.tuple2,(FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
                                          FStar_Pervasives_Native.tuple2,
        Prims.string Prims.list) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____20 = uenv in
      match uu____20 with
      | (dsenv,env) ->
          let uu____32 =
            match remaining with
            | intf::impl::remaining1 when
                FStar_Universal.needs_interleaving intf impl ->
                let uu____53 =
                  FStar_Universal.tc_one_file dsenv env
                    (FStar_Pervasives_Native.Some intf) impl in
                (match uu____53 with
                 | (uu____68,dsenv1,env1) ->
                     (((FStar_Pervasives_Native.Some intf), impl), dsenv1,
                       env1, remaining1))
            | intf_or_impl::remaining1 ->
                let uu____85 =
                  FStar_Universal.tc_one_file dsenv env
                    FStar_Pervasives_Native.None intf_or_impl in
                (match uu____85 with
                 | (uu____100,dsenv1,env1) ->
                     ((FStar_Pervasives_Native.None, intf_or_impl), dsenv1,
                       env1, remaining1))
            | [] -> failwith "Impossible" in
          (match uu____32 with
           | ((intf,impl),dsenv1,env1,remaining1) ->
               ((intf, impl), (dsenv1, env1), remaining1))
let tc_prims:
  Prims.unit ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____155  ->
    let uu____156 = FStar_Universal.tc_prims () in
    match uu____156 with | (uu____164,dsenv,env) -> (dsenv, env)
type env_t =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
type modul_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type stack_t = (env_t,modul_t) FStar_Pervasives_Native.tuple2 Prims.list
let pop uu____192 msg =
  match uu____192 with
  | (uu____196,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____203 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____208 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____213 -> false
let push:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    push_kind ->
      Prims.bool ->
        Prims.string ->
          (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun uu____230  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____230 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___194_241 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___194_241.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___194_241.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___194_241.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___194_241.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___194_241.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___194_241.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___194_241.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___194_241.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___194_241.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___194_241.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___194_241.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___194_241.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___194_241.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___194_241.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___194_241.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___194_241.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___194_241.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___194_241.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___194_241.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___194_241.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___194_241.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___194_241.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___194_241.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___194_241.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___194_241.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___194_241.FStar_TypeChecker_Env.is_native_tactic)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____248 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____248 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____257  ->
    match uu____257 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark uu____279 =
  match uu____279 with
  | (uu____282,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env1 = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env1))
let cleanup uu____297 =
  match uu____297 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____309  ->
    match uu____309 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv in
        let env1 = FStar_TypeChecker_Env.commit_mark env in (dsenv1, env1)
let check_frag:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,(FStar_ToSyntax_Env.env,
                                                                    FStar_TypeChecker_Env.env)
                                                                    FStar_Pervasives_Native.tuple2,
          Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option
  =
  fun uu____339  ->
    fun curmod  ->
      fun frag  ->
        match uu____339 with
        | (dsenv,env) ->
            (try
               let uu____377 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____377 with
               | FStar_Pervasives_Native.Some (m,dsenv1,env1) ->
                   let uu____399 =
                     let uu____406 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____406) in
                   FStar_Pervasives_Native.Some uu____399
               | uu____416 -> FStar_Pervasives_Native.None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____442 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____442 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____455 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____455 ->
                 ((let uu____457 =
                     let uu____461 =
                       let uu____464 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____464) in
                     [uu____461] in
                   FStar_TypeChecker_Err.add_errors env uu____457);
                  FStar_Pervasives_Native.None))
let deps_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____485 =
      FStar_List.partition
        (fun x  ->
           let uu____494 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____495 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____494 <> uu____495) deps in
    match uu____485 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____512 =
                  (let uu____515 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____515) ||
                    (let uu____517 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____517) in
                if uu____512
                then
                  let uu____518 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____518
                else ());
               FStar_Pervasives_Native.Some intf)
          | impl::[] -> FStar_Pervasives_Native.None
          | uu____521 ->
              ((let uu____524 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____524);
               FStar_Pervasives_Native.None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string FStar_Pervasives_Native.option,Prims.string,FStar_Util.time
                                                              FStar_Pervasives_Native.option,
    FStar_Util.time) FStar_Pervasives_Native.tuple4 Prims.list
let rec tc_deps:
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____562 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____573 =
                    let uu____574 = FStar_Options.lax () in
                    if uu____574 then LaxCheck else FullCheck in
                  push env uu____573 true "typecheck_modul" in
                let uu____576 = tc_one_file remaining env1 in
                (match uu____576 with
                 | ((intf,impl),env2,remaining1) ->
                     let uu____604 =
                       let intf_t =
                         match intf with
                         | FStar_Pervasives_Native.Some intf1 ->
                             let uu____612 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             FStar_Pervasives_Native.Some uu____612
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____604 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let update_deps:
  Prims.string ->
    modul_t ->
      stack_t ->
        env_t ->
          m_timestamps ->
            (stack_t,env_t,m_timestamps) FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (FStar_Pervasives_Native.Some
                    intf1,FStar_Pervasives_Native.Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> false
                 | (uu____686,uu____687) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | FStar_Pervasives_Native.None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____751 -> (false, depnames1))
                | FStar_Pervasives_Native.Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____768 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____815::ts3 ->
                    (pop env1 "";
                     (let uu____837 =
                        let uu____845 = FStar_List.hd stack in
                        let uu____850 = FStar_List.tl stack in
                        (uu____845, uu____850) in
                      match uu____837 with
                      | ((env2,uu____864),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____898 = ts_elt in
                  (match uu____898 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____916 = match_dep depnames intf impl in
                       (match uu____916 with
                        | (b,depnames') ->
                            let uu____927 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____927
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____939 =
                                 let uu____947 = FStar_List.hd st in
                                 let uu____952 = FStar_List.tl st in
                                 (uu____947, uu____952) in
                               match uu____939 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____992 = deps_of_our_file filename in
            match uu____992 with
            | (filenames,uu____1001) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___184_1033  ->
    match uu___184_1033 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1037 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1037
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1039 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1041 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1054 -> true
    | uu____1057 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1069 -> uu____1069
let js_fail expected got = raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___185_1090  ->
    match uu___185_1090 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___186_1096  ->
    match uu___186_1096 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list k uu___187_1117 =
  match uu___187_1117 with
  | FStar_Util.JsonList l -> FStar_List.map k l
  | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___188_1130  ->
    match uu___188_1130 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1146 = js_str s in
    match uu____1146 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1147 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1152 = js_str s in
    match uu____1152 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1153 -> js_fail "reduction rule" s
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
  FStar_Pervasives_Native.tuple5
  | AutoComplete of Prims.string
  | Lookup of
  (Prims.string,(Prims.string,Prims.int,Prims.int)
                  FStar_Pervasives_Native.tuple3
                  FStar_Pervasives_Native.option,Prims.string Prims.list)
  FStar_Pervasives_Native.tuple3
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Search of Prims.string
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1207 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1212 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1217 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1222 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1233 -> false
let __proj__Push__item___0:
  query' ->
    (push_kind,Prims.string,Prims.int,Prims.int,Prims.bool)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1262 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1284 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,(Prims.string,Prims.int,Prims.int)
                    FStar_Pervasives_Native.tuple3
                    FStar_Pervasives_Native.option,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1326 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1352 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1366 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let __proj__Mkquery__item__qq: query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
let __proj__Mkquery__item__qid: query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
let interactive_protocol_vernum: Prims.int = Prims.parse_int "1"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "compute";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/documentation";
  "lookup/definition";
  "pop";
  "peek";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____1395 -> true
    | uu____1396 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____1404 -> uu____1404
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1409 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1414 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1419 -> false
let try_assoc key a =
  let uu____1445 =
    FStar_Util.try_find
      (fun uu____1454  -> match uu____1454 with | (k,uu____1458) -> k = key)
      a in
  FStar_Util.map_option FStar_Pervasives_Native.snd uu____1445
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1473 =
          let uu____1474 =
            let uu____1475 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1475 in
          ProtocolViolation uu____1474 in
        { qq = uu____1473; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1496 = try_assoc key a in
      match uu____1496 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____1499 =
            let uu____1500 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____1500 in
          raise uu____1499 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____1509 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1509 js_str in
    try
      let query =
        let uu____1518 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____1518 js_str in
      let args =
        let uu____1523 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____1523 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____1536 = try_assoc k args in
        match uu____1536 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____1541 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____1542 =
              let uu____1548 =
                let uu____1549 = arg "kind" in
                FStar_All.pipe_right uu____1549 js_pushkind in
              let uu____1550 =
                let uu____1551 = arg "code" in
                FStar_All.pipe_right uu____1551 js_str in
              let uu____1552 =
                let uu____1553 = arg "line" in
                FStar_All.pipe_right uu____1553 js_int in
              let uu____1554 =
                let uu____1555 = arg "column" in
                FStar_All.pipe_right uu____1555 js_int in
              (uu____1548, uu____1550, uu____1552, uu____1554,
                (query = "peek")) in
            Push uu____1542
        | "push" ->
            let uu____1556 =
              let uu____1562 =
                let uu____1563 = arg "kind" in
                FStar_All.pipe_right uu____1563 js_pushkind in
              let uu____1564 =
                let uu____1565 = arg "code" in
                FStar_All.pipe_right uu____1565 js_str in
              let uu____1566 =
                let uu____1567 = arg "line" in
                FStar_All.pipe_right uu____1567 js_int in
              let uu____1568 =
                let uu____1569 = arg "column" in
                FStar_All.pipe_right uu____1569 js_int in
              (uu____1562, uu____1564, uu____1566, uu____1568,
                (query = "peek")) in
            Push uu____1556
        | "autocomplete" ->
            let uu____1570 =
              let uu____1571 = arg "partial-symbol" in
              FStar_All.pipe_right uu____1571 js_str in
            AutoComplete uu____1570
        | "lookup" ->
            let uu____1572 =
              let uu____1581 =
                let uu____1582 = arg "symbol" in
                FStar_All.pipe_right uu____1582 js_str in
              let uu____1583 =
                let uu____1588 =
                  let uu____1593 = try_arg "location" in
                  FStar_All.pipe_right uu____1593
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____1588
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____1625 =
                          let uu____1626 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____1626 js_str in
                        let uu____1627 =
                          let uu____1628 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____1628 js_int in
                        let uu____1629 =
                          let uu____1630 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____1630 js_int in
                        (uu____1625, uu____1627, uu____1629))) in
              let uu____1631 =
                let uu____1633 = arg "requested-info" in
                FStar_All.pipe_right uu____1633 (js_list js_str) in
              (uu____1581, uu____1583, uu____1631) in
            Lookup uu____1572
        | "compute" ->
            let uu____1640 =
              let uu____1645 =
                let uu____1646 = arg "term" in
                FStar_All.pipe_right uu____1646 js_str in
              let uu____1647 =
                let uu____1650 = try_arg "rules" in
                FStar_All.pipe_right uu____1650
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____1645, uu____1647) in
            Compute uu____1640
        | "search" ->
            let uu____1658 =
              let uu____1659 = arg "terms" in
              FStar_All.pipe_right uu____1659 js_str in
            Search uu____1658
        | uu____1660 ->
            let uu____1661 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____1661 in
      { qq = uu____1541; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___189_1671  ->
    match uu___189_1671 with
    | { qq = Push (SyntaxCheck ,uu____1672,uu____1673,uu____1674,false );
        qid;_} ->
        {
          qq =
            (ProtocolViolation
               "Cannot use 'kind': 'syntax' with 'query': 'push'");
          qid
        }
    | other -> other
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____1684 = FStar_Util.read_line stream in
      match uu____1684 with
      | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
      | FStar_Pervasives_Native.Some line ->
          let uu____1687 = FStar_Util.json_of_string line in
          (match uu____1687 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               let uu____1690 = unpack_interactive_query request in
               validate_interactive_query uu____1690)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___190_1700  ->
    match uu___190_1700 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____1707 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____1707
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt json_of_a opt_a =
  let uu____1731 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____1731
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____1737 =
      let uu____1739 =
        let uu____1740 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____1740 in
      let uu____1741 =
        let uu____1743 =
          let uu____1744 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____1744 in
        [uu____1743] in
      uu____1739 :: uu____1741 in
    FStar_Util.JsonList uu____1737
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____1757 =
          let uu____1761 =
            let uu____1765 =
              let uu____1768 = json_of_pos b in ("beg", uu____1768) in
            let uu____1769 =
              let uu____1773 =
                let uu____1776 = json_of_pos e in ("end", uu____1776) in
              [uu____1773] in
            uu____1765 :: uu____1769 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____1761 in
        FStar_Util.JsonAssoc uu____1757
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1789 = FStar_Range.file_of_use_range r in
    let uu____1790 = FStar_Range.start_of_use_range r in
    let uu____1791 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____1789 uu____1790 uu____1791
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1796 = FStar_Range.file_of_range r in
    let uu____1797 = FStar_Range.start_of_range r in
    let uu____1798 = FStar_Range.end_of_range r in
    json_of_range_fields uu____1796 uu____1797 uu____1798
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____1807 =
      let uu____1811 =
        let uu____1815 =
          let uu____1819 =
            let uu____1822 =
              let uu____1823 =
                let uu____1825 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____1829 = json_of_use_range r in [uu____1829] in
                let uu____1830 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____1834 = json_of_def_range r in [uu____1834]
                  | uu____1835 -> [] in
                FStar_List.append uu____1825 uu____1830 in
              FStar_Util.JsonList uu____1823 in
            ("ranges", uu____1822) in
          [uu____1819] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____1815 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____1811 in
    FStar_Util.JsonAssoc uu____1807
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  lr_typ: Prims.string FStar_Pervasives_Native.option;
  lr_doc: Prims.string FStar_Pervasives_Native.option;
  lr_def: Prims.string FStar_Pervasives_Native.option;}
let __proj__Mklookup_result__item__lr_name: lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_name
let __proj__Mklookup_result__item__lr_def_range:
  lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def_range
let __proj__Mklookup_result__item__lr_typ:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_typ
let __proj__Mklookup_result__item__lr_doc:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_doc
let __proj__Mklookup_result__item__lr_def:
  lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range;
        lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc;
        lr_def = __fname__lr_def;_} -> __fname__lr_def
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____1946 =
      let uu____1950 =
        let uu____1954 =
          let uu____1957 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____1957) in
        let uu____1958 =
          let uu____1962 =
            let uu____1965 =
              json_of_opt (fun _0_40  -> FStar_Util.JsonStr _0_40) lr.lr_typ in
            ("type", uu____1965) in
          let uu____1966 =
            let uu____1970 =
              let uu____1973 =
                json_of_opt (fun _0_41  -> FStar_Util.JsonStr _0_41)
                  lr.lr_doc in
              ("documentation", uu____1973) in
            let uu____1974 =
              let uu____1978 =
                let uu____1981 =
                  json_of_opt (fun _0_42  -> FStar_Util.JsonStr _0_42)
                    lr.lr_def in
                ("definition", uu____1981) in
              [uu____1978] in
            uu____1970 :: uu____1974 in
          uu____1962 :: uu____1966 in
        uu____1954 :: uu____1958 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____1950 in
    FStar_Util.JsonAssoc uu____1946
let json_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1999 =
      FStar_List.map (fun _0_43  -> FStar_Util.JsonStr _0_43)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_44  -> FStar_Util.JsonList _0_44) uu____1999 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____2013 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____2013);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> Prims.string -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", (FStar_Util.JsonStr contents))])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____2057  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____2060 =
        FStar_List.map (fun _0_45  -> FStar_Util.JsonStr _0_45)
          interactive_protocol_features in
      FStar_Util.JsonList uu____2060 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: json_of_protocol_info))
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_stack: stack_t;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_ts: m_timestamps;
  repl_stdin: FStar_Util.stream_reader;}
let __proj__Mkrepl_state__item__repl_line: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_line
let __proj__Mkrepl_state__item__repl_column: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_column
let __proj__Mkrepl_state__item__repl_fname: repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_fname
let __proj__Mkrepl_state__item__repl_stack: repl_state -> stack_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_stack
let __proj__Mkrepl_state__item__repl_curmod: repl_state -> modul_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_curmod
let __proj__Mkrepl_state__item__repl_env: repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_env
let __proj__Mkrepl_state__item__repl_ts: repl_state -> m_timestamps =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_ts
let __proj__Mkrepl_state__item__repl_stdin:
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin;_} ->
        __fname__repl_stdin
let json_of_repl_state:
  repl_state ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun st  ->
    let opts_and_defaults =
      let opt_docs =
        let uu____2208 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____2208 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____2229  ->
           match uu____2229 with
           | (k,v1) ->
               let uu____2239 = FStar_Options.get_option k in
               let uu____2240 = get_doc k in (k, uu____2239, uu____2240, v1))
        FStar_Options.defaults in
    let uu____2243 =
      let uu____2246 =
        let uu____2247 =
          FStar_List.map
            (fun uu____2260  ->
               match uu____2260 with
               | (uu____2267,fstname,uu____2269,uu____2270) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____2247 in
      ("loaded-dependencies", uu____2246) in
    let uu____2275 =
      let uu____2279 =
        let uu____2282 =
          let uu____2283 =
            FStar_List.map
              (fun uu____2296  ->
                 match uu____2296 with
                 | (name,value,doc1,dflt1) ->
                     let uu____2308 =
                       let uu____2312 =
                         let uu____2316 =
                           let uu____2319 = json_of_fstar_option value in
                           ("value", uu____2319) in
                         let uu____2320 =
                           let uu____2324 =
                             let uu____2327 = json_of_fstar_option dflt1 in
                             ("default", uu____2327) in
                           let uu____2328 =
                             let uu____2332 =
                               let uu____2335 =
                                 json_of_opt
                                   (fun _0_46  -> FStar_Util.JsonStr _0_46)
                                   doc1 in
                               ("documentation", uu____2335) in
                             [uu____2332] in
                           uu____2324 :: uu____2328 in
                         uu____2316 :: uu____2320 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____2312 in
                     FStar_Util.JsonAssoc uu____2308) opts_and_defaults in
          FStar_Util.JsonList uu____2283 in
        ("options", uu____2282) in
      [uu____2279] in
    uu____2243 :: uu____2275
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
let run_describe_repl st =
  let uu____2411 =
    let uu____2414 =
      let uu____2415 = json_of_repl_state st in
      FStar_Util.JsonAssoc uu____2415 in
    (QueryOK, uu____2414) in
  (uu____2411, (FStar_Util.Inl st))
let run_protocol_violation st message =
  ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
    (FStar_Util.Inl st))
let run_pop st =
  match st.repl_stack with
  | [] ->
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
  | (env,curmod)::stack ->
      (pop st.repl_env "#pop";
       if (FStar_List.length stack) = (FStar_List.length st.repl_ts)
       then cleanup env
       else ();
       ((QueryOK, FStar_Util.JsonNull),
         (FStar_Util.Inl
            ((let uu___201_2504 = st in
              {
                repl_line = (uu___201_2504.repl_line);
                repl_column = (uu___201_2504.repl_column);
                repl_fname = (uu___201_2504.repl_fname);
                repl_stack = stack;
                repl_curmod = curmod;
                repl_env = env;
                repl_ts = (uu___201_2504.repl_ts);
                repl_stdin = (uu___201_2504.repl_stdin)
              })))))
let run_push st kind text1 line column1 peek_only =
  let uu____2550 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____2550 with
  | (stack,env,ts) ->
      let uu____2563 =
        if (FStar_List.length stack) = (FStar_List.length ts)
        then
          let uu____2590 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____2590)
        else (false, (stack, env, ts)) in
      (match uu____2563 with
       | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
           let stack2 = (env1, (st.repl_curmod)) :: stack1 in
           let env2 = push env1 kind restore_cmd_line_options1 "#push" in
           let env_mark = mark env2 in
           let frag =
             {
               FStar_Parser_ParseIt.frag_text = text1;
               FStar_Parser_ParseIt.frag_line = line;
               FStar_Parser_ParseIt.frag_col = column1
             } in
           let res = check_frag env_mark st.repl_curmod (frag, false) in
           let errors =
             let uu____2637 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____2637 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___202_2643 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___202_2643.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___202_2643.repl_curmod);
                 repl_env = (uu___202_2643.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___202_2643.repl_stdin)
               } in
             match res with
             | FStar_Pervasives_Native.Some (curmod,env3,nerrs) when
                 (nerrs = (Prims.parse_int "0")) && (peek_only = false) ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___203_2673 = st' in
                       {
                         repl_line = (uu___203_2673.repl_line);
                         repl_column = (uu___203_2673.repl_column);
                         repl_fname = (uu___203_2673.repl_fname);
                         repl_stack = (uu___203_2673.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___203_2673.repl_ts);
                         repl_stdin = (uu___203_2673.repl_stdin)
                       })))
             | uu____2674 ->
                 let env3 = reset_mark env_mark in
                 let uu____2685 =
                   run_pop
                     (let uu___204_2693 = st' in
                      {
                        repl_line = (uu___204_2693.repl_line);
                        repl_column = (uu___204_2693.repl_column);
                        repl_fname = (uu___204_2693.repl_fname);
                        repl_stack = (uu___204_2693.repl_stack);
                        repl_curmod = (uu___204_2693.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___204_2693.repl_ts);
                        repl_stdin = (uu___204_2693.repl_stdin)
                      }) in
                 (match uu____2685 with
                  | (uu____2700,st'') ->
                      let status = if peek_only then QueryOK else QueryNOK in
                      ((status, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____2759 = st.repl_env in
  match uu____2759 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____2779 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____2779 in
        let lid1 =
          let uu____2782 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____2782 in
        let uu____2785 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____2785
          (FStar_Util.map_option
             (fun uu____2815  ->
                match uu____2815 with
                | ((uu____2825,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____2837 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____2837
          (FStar_Util.map_option FStar_Pervasives_Native.fst) in
      let def_of_lid lid =
        let uu____2854 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
        FStar_Util.bind_opt uu____2854
          (fun uu___191_2879  ->
             match uu___191_2879 with
             | (FStar_Util.Inr (se,uu____2891),uu____2892) ->
                 let uu____2907 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Pervasives_Native.Some uu____2907
             | uu____2908 -> FStar_Pervasives_Native.None) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____2937  ->
             match uu____2937 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | FStar_Pervasives_Native.Some uu____2963 -> info_at_pos_opt
        | FStar_Pervasives_Native.None  ->
            if symbol = ""
            then FStar_Pervasives_Native.None
            else info_of_lid_str symbol in
      let response =
        match info_opt with
        | FStar_Pervasives_Native.None  -> (QueryNOK, FStar_Util.JsonNull)
        | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
            let name =
              match name_or_lid with
              | FStar_Util.Inl name -> name
              | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
            let typ_str =
              if FStar_List.mem "type" requested_info
              then
                let uu____3019 = FStar_Syntax_Print.term_to_string typ in
                FStar_Pervasives_Native.Some uu____3019
              else FStar_Pervasives_Native.None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____3025 -> FStar_Pervasives_Native.None in
            let def_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "definition" requested_info ->
                  def_of_lid lid
              | uu____3032 -> FStar_Pervasives_Native.None in
            let def_range =
              if FStar_List.mem "defined-at" requested_info
              then FStar_Pervasives_Native.Some rng
              else FStar_Pervasives_Native.None in
            let result =
              {
                lr_name = name;
                lr_def_range = def_range;
                lr_typ = typ_str;
                lr_doc = doc_str;
                lr_def = def_str
              } in
            let uu____3040 = json_of_lookup_result result in
            (QueryOK, uu____3040) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____3066 = st.repl_env in
  match uu____3066 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____3096) ->
            FStar_Pervasives_Native.Some ([], (Prims.parse_int "0"))
        | (uu____3104,[]) -> FStar_Pervasives_Native.None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] ->
                   FStar_Pervasives_Native.Some
                     (candidate, (FStar_String.length hs))
               | uu____3136 ->
                   let uu____3138 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____3138
                     (FStar_Util.map_option
                        (fun uu____3160  ->
                           match uu____3160 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else FStar_Pervasives_Native.None in
      let rec locate_match needle candidate =
        let uu____3199 = measure_anchored_match needle candidate in
        match uu____3199 with
        | FStar_Pervasives_Native.Some (matched,n1) ->
            FStar_Pervasives_Native.Some ([], matched, n1)
        | FStar_Pervasives_Native.None  ->
            (match candidate with
             | [] -> FStar_Pervasives_Native.None
             | hc::tc ->
                 let uu____3241 = locate_match needle tc in
                 FStar_All.pipe_right uu____3241
                   (FStar_Util.map_option
                      (fun uu____3274  ->
                         match uu____3274 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____3300 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____3300 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____3329 =
        match uu____3329 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____3347::[] -> true
              | uu____3348 -> false in
            let uu____3350 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____3350 with
             | (stripped_ns,shortened) ->
                 let uu____3365 = str_of_ids shortened in
                 let uu____3366 = str_of_ids matched in
                 let uu____3367 = str_of_ids stripped_ns in
                 (uu____3365, uu____3366, uu____3367, match_len)) in
      let prepare_candidate uu____3378 =
        match uu____3378 with
        | (prefix1,matched,stripped_ns,match_len) ->
            if prefix1 = ""
            then (matched, stripped_ns, match_len)
            else
              ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                stripped_ns,
                (((FStar_String.length prefix1) + match_len) +
                   (Prims.parse_int "1"))) in
      let needle = FStar_Util.split search_term "." in
      let all_lidents_in_env = FStar_TypeChecker_Env.lidents tcenv in
      let matches =
        let case_a_find_transitive_includes orig_ns m id =
          let exported_names =
            FStar_ToSyntax_Env.transitive_exported_ids dsenv m in
          let matched_length =
            FStar_List.fold_left
              (fun out  ->
                 fun s  ->
                   ((FStar_String.length s) + out) + (Prims.parse_int "1"))
              (FStar_String.length id) orig_ns in
          FStar_All.pipe_right exported_names
            (FStar_List.filter_map
               (fun n1  ->
                  if FStar_Util.starts_with n1 id
                  then
                    let lid =
                      FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m)
                        (FStar_Ident.id_of_text n1) in
                    let uu____3473 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____3483 =
                           let uu____3485 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____3485
                             [fqn.FStar_Ident.ident] in
                         ([], uu____3483, matched_length)) uu____3473
                  else FStar_Pervasives_Native.None)) in
        let case_b_find_matches_in_env uu____3504 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____3545  ->
                  match uu____3545 with
                  | (ns,id,uu____3553) ->
                      let uu____3558 =
                        let uu____3560 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____3560 in
                      (match uu____3558 with
                       | FStar_Pervasives_Native.None  -> false
                       | FStar_Pervasives_Native.Some l ->
                           let uu____3562 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____3562))) in
        let uu____3563 = FStar_Util.prefix needle in
        match uu____3563 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____3588 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____3591 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____3591 with
                   | FStar_Pervasives_Native.None  ->
                       case_b_find_matches_in_env ()
                   | FStar_Pervasives_Native.Some m ->
                       case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____3626 = shorten_namespace x in
                    prepare_candidate uu____3626)) in
      let json_candidates =
        let uu____3633 =
          FStar_Util.sort_with
            (fun uu____3649  ->
               fun uu____3650  ->
                 match (uu____3649, uu____3650) with
                 | ((cd1,ns1,uu____3665),(cd2,ns2,uu____3668)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_47 when _0_47 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____3683  ->
             match uu____3683 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____3633 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_compute st term rules =
  let run_and_rewind st1 task =
    let env_mark = mark st1.repl_env in
    let results = task st1 in
    let env = reset_mark env_mark in
    let st' =
      let uu___205_3757 = st1 in
      {
        repl_line = (uu___205_3757.repl_line);
        repl_column = (uu___205_3757.repl_column);
        repl_fname = (uu___205_3757.repl_fname);
        repl_stack = (uu___205_3757.repl_stack);
        repl_curmod = (uu___205_3757.repl_curmod);
        repl_env = env;
        repl_ts = (uu___205_3757.repl_ts);
        repl_stdin = (uu___205_3757.repl_stdin)
      } in
    (results, (FStar_Util.Inl st')) in
  let dummy_let_fragment term1 =
    let dummy_decl = FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
    {
      FStar_Parser_ParseIt.frag_text = dummy_decl;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    } in
  let normalize_term1 tcenv rules1 t =
    FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
  let find_let_body ses =
    match ses with
    | {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
          ((uu____3789,{ FStar_Syntax_Syntax.lbname = uu____3790;
                         FStar_Syntax_Syntax.lbunivs = uu____3791;
                         FStar_Syntax_Syntax.lbtyp = uu____3792;
                         FStar_Syntax_Syntax.lbeff = uu____3793;
                         FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____3795);
        FStar_Syntax_Syntax.sigrng = uu____3796;
        FStar_Syntax_Syntax.sigquals = uu____3797;
        FStar_Syntax_Syntax.sigmeta = uu____3798;
        FStar_Syntax_Syntax.sigattrs = uu____3799;_}::[] ->
        FStar_Pervasives_Native.Some def
    | uu____3817 -> FStar_Pervasives_Native.None in
  let parse1 frag =
    let uu____3827 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____3827 with
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____3840) ->
        FStar_Pervasives_Native.Some decls
    | uu____3863 -> FStar_Pervasives_Native.None in
  let desugar dsenv decls =
    let uu____3883 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
    FStar_Pervasives_Native.snd uu____3883 in
  let typecheck tcenv decls =
    let uu____3896 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
    match uu____3896 with | (ses,uu____3904,uu____3905) -> ses in
  let rules1 =
    FStar_List.append
      (match rules with
       | FStar_Pervasives_Native.Some rules1 -> rules1
       | FStar_Pervasives_Native.None  ->
           [FStar_TypeChecker_Normalize.Beta;
           FStar_TypeChecker_Normalize.Iota;
           FStar_TypeChecker_Normalize.Zeta;
           FStar_TypeChecker_Normalize.UnfoldUntil
             FStar_Syntax_Syntax.Delta_constant])
      [FStar_TypeChecker_Normalize.Inlining;
      FStar_TypeChecker_Normalize.Eager_unfolding;
      FStar_TypeChecker_Normalize.Primops] in
  run_and_rewind st
    (fun st1  ->
       let uu____3924 = st1.repl_env in
       match uu____3924 with
       | (dsenv,tcenv) ->
           let frag = dummy_let_fragment term in
           (match st1.repl_curmod with
            | FStar_Pervasives_Native.None  ->
                (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
            | uu____3932 ->
                let uu____3933 = parse1 frag in
                (match uu____3933 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Count not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     (try
                        let decls1 = desugar dsenv decls in
                        let ses = typecheck tcenv decls1 in
                        match find_let_body ses with
                        | FStar_Pervasives_Native.None  ->
                            (QueryNOK,
                              (FStar_Util.JsonStr
                                 "Typechecking yielded an unexpected term"))
                        | FStar_Pervasives_Native.Some def ->
                            let normalized = normalize_term1 tcenv rules1 def in
                            let uu____3963 =
                              let uu____3964 =
                                FStar_Syntax_Print.term_to_string normalized in
                              FStar_Util.JsonStr uu____3964 in
                            (QueryOK, uu____3963)
                      with
                      | e ->
                          let uu____3972 =
                            let uu____3973 = FStar_Errors.issue_of_exn e in
                            match uu____3973 with
                            | FStar_Pervasives_Native.Some issue ->
                                let uu____3976 =
                                  FStar_Errors.format_issue issue in
                                FStar_Util.JsonStr uu____3976
                            | FStar_Pervasives_Native.None  -> raise e in
                          (QueryNOK, uu____3972)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____3998 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____4012 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate: search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
let __proj__Mksearch_term__item__st_term: search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
let st_cost: search_term' -> Prims.int =
  fun uu___192_4036  ->
    match uu___192_4036 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____4120 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____4125 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____4120; sc_fvars = uu____4125 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____4145 = FStar_ST.read sc.sc_typ in
      match uu____4145 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____4154 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____4154 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____4170,typ),uu____4172) ->
                typ in
          (FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some typ); typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____4194 = FStar_ST.read sc.sc_fvars in
      match uu____4194 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____4208 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____4208 in
          (FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some fv); fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____4228 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____4228 in
        let uu____4229 =
          let uu____4233 =
            let uu____4236 =
              let uu____4237 =
                let uu____4238 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____4238.FStar_Ident.str in
              FStar_Util.JsonStr uu____4237 in
            ("lid", uu____4236) in
          [uu____4233; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____4229
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____4252 -> true
    | uu____4253 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____4261 -> uu____4261
let run_search st search_str =
  let uu____4283 = st.repl_env in
  match uu____4283 with
  | (dsenv,tcenv) ->
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____4304 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____4304 in
        found <> term.st_negate in
      let parse1 search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-" in
          let term1 =
            if negate
            then FStar_Util.substring_from term (Prims.parse_int "1")
            else term in
          let beg_quote = FStar_Util.starts_with term1 "\"" in
          let end_quote = FStar_Util.ends_with term1 "\"" in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.parse_int "2")
            then raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.parse_int "1")
                ((FStar_String.length term1) - (Prims.parse_int "2")) in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____4338 =
                let uu____4339 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____4339 in
              raise uu____4338
            else
              if beg_quote
              then
                (let uu____4341 = strip_quotes term1 in
                 NameContainsStr uu____4341)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____4344 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                     lid in
                 match uu____4344 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4346 =
                       let uu____4347 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____4347 in
                     raise uu____4346
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____4362 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____4362 in
      let results =
        try
          let terms = parse1 search_str in
          let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
          let all_candidates = FStar_List.map sc_of_lid all_lidents in
          let matches_all candidate =
            FStar_List.for_all (st_matches candidate) terms in
          let cmp r1 r2 =
            FStar_Util.compare (r1.sc_lid).FStar_Ident.str
              (r2.sc_lid).FStar_Ident.str in
          let results = FStar_List.filter matches_all all_candidates in
          let sorted1 = FStar_Util.sort_with cmp results in
          let js =
            FStar_Options.with_saved_options
              (fun uu____4411  ->
                 FStar_Options.set_option "print_effect_args"
                   (FStar_Options.Bool true);
                 FStar_List.map (json_of_search_result dsenv tcenv) sorted1) in
          match results with
          | [] ->
              let kwds =
                let uu____4416 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____4416 in
              let uu____4418 =
                let uu____4419 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____4419 in
              raise uu____4418
          | uu____4422 -> (QueryOK, (FStar_Util.JsonList js))
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun uu___193_4454  ->
      match uu___193_4454 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek1) -> run_push st kind text1 l c peek1
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | ProtocolViolation query -> run_protocol_violation st query
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query = read_interactive_query st.repl_stdin in
    let uu____4493 = let uu____4500 = run_query st in uu____4500 query.qq in
    match uu____4493 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____4530 = let uu____4532 = FStar_ST.read issues in e :: uu____4532 in
    FStar_ST.write issues uu____4530 in
  let count_errors uu____4543 =
    let uu____4544 =
      let uu____4546 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____4546 in
    FStar_List.length uu____4544 in
  let report1 uu____4559 =
    let uu____4560 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____4560 in
  let clear1 uu____4568 = FStar_ST.write issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo = (write_message "info");
    FStar_Util.printer_prwarning = (write_message "warning");
    FStar_Util.printer_prerror = (write_message "error")
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____4581 = deps_of_our_file filename in
     match uu____4581 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____4595 =
           tc_deps FStar_Pervasives_Native.None [] env filenames [] in
         (match uu____4595 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____4611 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4612 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4611 uu____4612 in
              let env2 =
                let uu____4616 =
                  FStar_TypeChecker_Env.set_range
                    (FStar_Pervasives_Native.snd env1) initial_range in
                ((FStar_Pervasives_Native.fst env1), uu____4616) in
              let env3 =
                match maybe_intf with
                | FStar_Pervasives_Native.Some intf ->
                    FStar_Universal.load_interface_decls env2 intf
                | FStar_Pervasives_Native.None  -> env2 in
              let init_st =
                let uu____4624 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = FStar_Pervasives_Native.None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____4624
                } in
              (FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.enable
                 true;
               (let uu____4626 =
                  (FStar_Options.record_hints ()) ||
                    (FStar_Options.use_hints ()) in
                if uu____4626
                then
                  let uu____4627 =
                    let uu____4628 = FStar_Options.file_list () in
                    FStar_List.hd uu____4628 in
                  FStar_SMTEncoding_Solver.with_hints_db uu____4627
                    (fun uu____4631  -> go init_st)
                else go init_st))))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____4640 =
       let uu____4641 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4641 in
     if uu____4640
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e -> (FStar_Errors.set_handler FStar_Errors.default_handler; raise e))