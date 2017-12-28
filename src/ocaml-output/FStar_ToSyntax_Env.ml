open Prims
type local_binding =
  (FStar_Ident.ident,FStar_Syntax_Syntax.bv,Prims.bool)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type rec_binding =
  (FStar_Ident.ident,FStar_Ident.lid,FStar_Syntax_Syntax.delta_depth)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type module_abbrev =
  (FStar_Ident.ident,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
[@@deriving show]
type open_kind =
  | Open_module
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____20 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____24 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}[@@deriving show]
let __proj__Mkrecord_or_dc__item__typename:
  record_or_dc -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
let __proj__Mkrecord_or_dc__item__constrname:
  record_or_dc -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
let __proj__Mkrecord_or_dc__item__parms:
  record_or_dc -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
let __proj__Mkrecord_or_dc__item__fields:
  record_or_dc ->
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
let __proj__Mkrecord_or_dc__item__is_private_or_abstract:
  record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
let __proj__Mkrecord_or_dc__item__is_record: record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_record
type scope_mod =
  | Local_binding of local_binding
  | Rec_binding of rec_binding
  | Module_abbrev of module_abbrev
  | Open_module_or_namespace of open_module_or_namespace
  | Top_level_def of FStar_Ident.ident
  | Record_or_dc of record_or_dc[@@deriving show]
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____189 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____201 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____213 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____225 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____237 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____249 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field[@@deriving show]
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____262 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____266 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  syntax_only: Prims.bool;
  ds_hooks: dsenv_hooks;}[@@deriving show]
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> Prims.unit;
  ds_push_include_hook: env -> FStar_Ident.lident -> Prims.unit;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit;}[@@deriving
                                                                    show]
let __proj__Mkenv__item__curmodule:
  env -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmodule
let __proj__Mkenv__item__curmonad:
  env -> FStar_Ident.ident FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__curmonad
let __proj__Mkenv__item__modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__modules
let __proj__Mkenv__item__scope_mods: env -> scope_mod Prims.list =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__scope_mods
let __proj__Mkenv__item__exported_ids: env -> exported_id_set FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__exported_ids
let __proj__Mkenv__item__trans_exported_ids:
  env -> exported_id_set FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__trans_exported_ids
let __proj__Mkenv__item__includes:
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__includes
let __proj__Mkenv__item__sigaccum: env -> FStar_Syntax_Syntax.sigelts =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigaccum
let __proj__Mkenv__item__sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__sigmap
let __proj__Mkenv__item__iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__iface
let __proj__Mkenv__item__admitted_iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__admitted_iface
let __proj__Mkenv__item__expect_typ: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__expect_typ
let __proj__Mkenv__item__docs: env -> FStar_Parser_AST.fsdoc FStar_Util.smap
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__docs
let __proj__Mkenv__item__remaining_iface_decls:
  env ->
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__remaining_iface_decls
let __proj__Mkenv__item__syntax_only: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__syntax_only
let __proj__Mkenv__item__ds_hooks: env -> dsenv_hooks =
  fun projectee  ->
    match projectee with
    | { curmodule = __fname__curmodule; curmonad = __fname__curmonad;
        modules = __fname__modules; scope_mods = __fname__scope_mods;
        exported_ids = __fname__exported_ids;
        trans_exported_ids = __fname__trans_exported_ids;
        includes = __fname__includes; sigaccum = __fname__sigaccum;
        sigmap = __fname__sigmap; iface = __fname__iface;
        admitted_iface = __fname__admitted_iface;
        expect_typ = __fname__expect_typ; docs = __fname__docs;
        remaining_iface_decls = __fname__remaining_iface_decls;
        syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks;_}
        -> __fname__ds_hooks
let __proj__Mkdsenv_hooks__item__ds_push_open_hook:
  dsenv_hooks -> env -> open_module_or_namespace -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
let __proj__Mkdsenv_hooks__item__ds_push_include_hook:
  dsenv_hooks -> env -> FStar_Ident.lident -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook:
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
let default_ds_hooks: dsenv_hooks =
  {
    ds_push_open_hook = (fun uu____1535  -> fun uu____1536  -> ());
    ds_push_include_hook = (fun uu____1539  -> fun uu____1540  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1544  -> fun uu____1545  -> fun uu____1546  -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1571 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1599 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___110_1625 = env in
      {
        curmodule = (uu___110_1625.curmodule);
        curmonad = (uu___110_1625.curmonad);
        modules = (uu___110_1625.modules);
        scope_mods = (uu___110_1625.scope_mods);
        exported_ids = (uu___110_1625.exported_ids);
        trans_exported_ids = (uu___110_1625.trans_exported_ids);
        includes = (uu___110_1625.includes);
        sigaccum = (uu___110_1625.sigaccum);
        sigmap = (uu___110_1625.sigmap);
        iface = b;
        admitted_iface = (uu___110_1625.admitted_iface);
        expect_typ = (uu___110_1625.expect_typ);
        docs = (uu___110_1625.docs);
        remaining_iface_decls = (uu___110_1625.remaining_iface_decls);
        syntax_only = (uu___110_1625.syntax_only);
        ds_hooks = (uu___110_1625.ds_hooks)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___111_1635 = e in
      {
        curmodule = (uu___111_1635.curmodule);
        curmonad = (uu___111_1635.curmonad);
        modules = (uu___111_1635.modules);
        scope_mods = (uu___111_1635.scope_mods);
        exported_ids = (uu___111_1635.exported_ids);
        trans_exported_ids = (uu___111_1635.trans_exported_ids);
        includes = (uu___111_1635.includes);
        sigaccum = (uu___111_1635.sigaccum);
        sigmap = (uu___111_1635.sigmap);
        iface = (uu___111_1635.iface);
        admitted_iface = b;
        expect_typ = (uu___111_1635.expect_typ);
        docs = (uu___111_1635.docs);
        remaining_iface_decls = (uu___111_1635.remaining_iface_decls);
        syntax_only = (uu___111_1635.syntax_only);
        ds_hooks = (uu___111_1635.ds_hooks)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___112_1645 = e in
      {
        curmodule = (uu___112_1645.curmodule);
        curmonad = (uu___112_1645.curmonad);
        modules = (uu___112_1645.modules);
        scope_mods = (uu___112_1645.scope_mods);
        exported_ids = (uu___112_1645.exported_ids);
        trans_exported_ids = (uu___112_1645.trans_exported_ids);
        includes = (uu___112_1645.includes);
        sigaccum = (uu___112_1645.sigaccum);
        sigmap = (uu___112_1645.sigmap);
        iface = (uu___112_1645.iface);
        admitted_iface = (uu___112_1645.admitted_iface);
        expect_typ = b;
        docs = (uu___112_1645.docs);
        remaining_iface_decls = (uu___112_1645.remaining_iface_decls);
        syntax_only = (uu___112_1645.syntax_only);
        ds_hooks = (uu___112_1645.ds_hooks)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1660 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1660 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1666 =
            let uu____1667 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1667 in
          FStar_All.pipe_right uu____1666 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let open_modules_and_namespaces: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___78_1942  ->
         match uu___78_1942 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1947 -> FStar_Pervasives_Native.None) env.scope_mods
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___113_1954 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___113_1954.curmonad);
        modules = (uu___113_1954.modules);
        scope_mods = (uu___113_1954.scope_mods);
        exported_ids = (uu___113_1954.exported_ids);
        trans_exported_ids = (uu___113_1954.trans_exported_ids);
        includes = (uu___113_1954.includes);
        sigaccum = (uu___113_1954.sigaccum);
        sigmap = (uu___113_1954.sigmap);
        iface = (uu___113_1954.iface);
        admitted_iface = (uu___113_1954.admitted_iface);
        expect_typ = (uu___113_1954.expect_typ);
        docs = (uu___113_1954.docs);
        remaining_iface_decls = (uu___113_1954.remaining_iface_decls);
        syntax_only = (uu___113_1954.syntax_only);
        ds_hooks = (uu___113_1954.ds_hooks)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let iface_decls:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1969 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2003  ->
                match uu____2003 with
                | (m,uu____2011) -> FStar_Ident.lid_equals l m)) in
      match uu____1969 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2028,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2055 =
          FStar_List.partition
            (fun uu____2085  ->
               match uu____2085 with
               | (m,uu____2093) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____2055 with
        | (uu____2098,rest) ->
            let uu___114_2132 = env in
            {
              curmodule = (uu___114_2132.curmodule);
              curmonad = (uu___114_2132.curmonad);
              modules = (uu___114_2132.modules);
              scope_mods = (uu___114_2132.scope_mods);
              exported_ids = (uu___114_2132.exported_ids);
              trans_exported_ids = (uu___114_2132.trans_exported_ids);
              includes = (uu___114_2132.includes);
              sigaccum = (uu___114_2132.sigaccum);
              sigmap = (uu___114_2132.sigmap);
              iface = (uu___114_2132.iface);
              admitted_iface = (uu___114_2132.admitted_iface);
              expect_typ = (uu___114_2132.expect_typ);
              docs = (uu___114_2132.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___114_2132.syntax_only);
              ds_hooks = (uu___114_2132.ds_hooks)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2151 = current_module env in qual uu____2151 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2153 =
            let uu____2154 = current_module env in qual uu____2154 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2153 id1
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___115_2164 = env in
      {
        curmodule = (uu___115_2164.curmodule);
        curmonad = (uu___115_2164.curmonad);
        modules = (uu___115_2164.modules);
        scope_mods = (uu___115_2164.scope_mods);
        exported_ids = (uu___115_2164.exported_ids);
        trans_exported_ids = (uu___115_2164.trans_exported_ids);
        includes = (uu___115_2164.includes);
        sigaccum = (uu___115_2164.sigaccum);
        sigmap = (uu___115_2164.sigmap);
        iface = (uu___115_2164.iface);
        admitted_iface = (uu___115_2164.admitted_iface);
        expect_typ = (uu___115_2164.expect_typ);
        docs = (uu___115_2164.docs);
        remaining_iface_decls = (uu___115_2164.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___115_2164.ds_hooks)
      }
let ds_hooks: env -> dsenv_hooks = fun env  -> env.ds_hooks
let set_ds_hooks: env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___116_2174 = env in
      {
        curmodule = (uu___116_2174.curmodule);
        curmonad = (uu___116_2174.curmonad);
        modules = (uu___116_2174.modules);
        scope_mods = (uu___116_2174.scope_mods);
        exported_ids = (uu___116_2174.exported_ids);
        trans_exported_ids = (uu___116_2174.trans_exported_ids);
        includes = (uu___116_2174.includes);
        sigaccum = (uu___116_2174.sigaccum);
        sigmap = (uu___116_2174.sigmap);
        iface = (uu___116_2174.iface);
        admitted_iface = (uu___116_2174.admitted_iface);
        expect_typ = (uu___116_2174.expect_typ);
        docs = (uu___116_2174.docs);
        remaining_iface_decls = (uu___116_2174.remaining_iface_decls);
        syntax_only = (uu___116_2174.syntax_only);
        ds_hooks = hooks
      }
let new_sigmap: 'Auu____2177 . Prims.unit -> 'Auu____2177 FStar_Util.smap =
  fun uu____2183  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____2186  ->
    let uu____2187 = new_sigmap () in
    let uu____2190 = new_sigmap () in
    let uu____2193 = new_sigmap () in
    let uu____2204 = new_sigmap () in
    let uu____2215 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2187;
      trans_exported_ids = uu____2190;
      includes = uu____2193;
      sigaccum = [];
      sigmap = uu____2204;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2215;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks
    }
let sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____2247  ->
         match uu____2247 with
         | (m,uu____2253) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___117_2261 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___117_2261.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___118_2262 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___118_2262.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___118_2262.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let unmangleOpName:
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun id1  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2349  ->
           match uu____2349 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2372 =
                   let uu____2373 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2373 dd dq in
                 FStar_Pervasives_Native.Some uu____2372
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore[@@deriving show]
let uu___is_Cont_ok: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2416 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2445 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2459 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___79_2482  ->
      match uu___79_2482 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2495 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2495 cont_t) -> 'Auu____2495 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2541  ->
                   match uu____2541 with
                   | (f,uu____2549) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
let get_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___80_2595  ->
    match uu___80_2595 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes:
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind  ->
    fun find_in_module  ->
      fun find_in_module_default  ->
        fun env  ->
          fun ns  ->
            fun id1  ->
              let idstr = id1.FStar_Ident.idText in
              let rec aux uu___81_2651 =
                match uu___81_2651 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2662 = get_exported_id_set env mname in
                      match uu____2662 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2683 = mex eikind in
                            FStar_ST.op_Bang uu____2683 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2942 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2942 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3047 = qual modul id1 in
                        find_in_module uu____3047
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3051 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___82_3056  ->
    match uu___82_3056 with
    | Exported_id_field  -> true
    | uu____3057 -> false
let try_lookup_id'':
  'a .
    env ->
      FStar_Ident.ident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id1  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___83_3159 =
                    match uu___83_3159 with
                    | (id',uu____3161,uu____3162) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___84_3166 =
                    match uu___84_3166 with
                    | (id',uu____3168,uu____3169) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____3173 = current_module env in
                    FStar_Ident.ids_of_lid uu____3173 in
                  let proc uu___85_3179 =
                    match uu___85_3179 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3187 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3187 id1
                    | uu____3192 -> Cont_ignore in
                  let rec aux uu___86_3200 =
                    match uu___86_3200 with
                    | a::q ->
                        let uu____3209 = proc a in
                        option_of_cont (fun uu____3213  -> aux q) uu____3209
                    | [] ->
                        let uu____3214 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____3218  -> FStar_Pervasives_Native.None)
                          uu____3214 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3223 'Auu____3224 .
    FStar_Range.range ->
      ('Auu____3224,FStar_Syntax_Syntax.bv,'Auu____3223)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3223)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3242  ->
      match uu____3242 with
      | (id',x,mut) -> let uu____3252 = bv_to_name x r in (uu____3252, mut)
let find_in_module:
  'Auu____3258 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3258)
          -> 'Auu____3258 -> 'Auu____3258
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3293 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3293 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id1  ->
      let uu____3329 = unmangleOpName id1 in
      match uu____3329 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3355 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3369 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3369) (fun uu____3379  -> Cont_fail)
            (fun uu____3385  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3400  -> fun uu____3401  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3416  -> fun uu____3417  -> Cont_fail)
let lookup_default_id:
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env  ->
    fun id1  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3487 ->
                let lid = qualify env id1 in
                let uu____3489 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3489 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3513 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3513
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3536 = current_module env in qual uu____3536 id1 in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3546 = current_module env in
           FStar_Ident.lid_equals lid uu____3546)
        ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let resolve_module_name:
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___87_3578 =
          match uu___87_3578 with
          | [] ->
              let uu____3583 = module_is_defined env lid in
              if uu____3583
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3592 =
                  let uu____3595 = FStar_Ident.path_of_lid ns in
                  let uu____3598 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3595 uu____3598 in
                FStar_Ident.lid_of_path uu____3592
                  (FStar_Ident.range_of_lid lid) in
              let uu____3601 = module_is_defined env new_lid in
              if uu____3601
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3607 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3614::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3627 =
          let uu____3628 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3628 in
        if uu____3627
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3630 =
                let uu____3635 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3635) in
              FStar_Errors.raise_error uu____3630
                (FStar_Ident.range_of_lid ns_original)))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3643 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3647 = resolve_module_name env modul_orig true in
          (match uu____3647 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3651 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___88_3662  ->
           match uu___88_3662 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3664 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id1 =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1 in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some
              ((FStar_List.rev (id1 :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3753 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3753
                   (FStar_Util.map_option
                      (fun uu____3803  ->
                         match uu____3803 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let uu____3834 =
          is_full_path &&
            (let uu____3836 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3836) in
        if uu____3834
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3866 = aux ns_rev_prefix ns_last_id in
               (match uu____3866 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3925 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3925 with
      | (uu____3934,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'':
  'a .
    env ->
      FStar_Ident.lident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  match lid.FStar_Ident.ns with
                  | uu____4042::uu____4043 ->
                      let uu____4046 =
                        let uu____4049 =
                          let uu____4050 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____4050
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____4049 true in
                      (match uu____4046 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4054 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____4058  -> FStar_Pervasives_Native.None)
                             uu____4054)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___89_4076  ->
      match uu___89_4076 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces':
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt,Prims.bool)
                 FStar_Pervasives_Native.tuple2 ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____4175 = k_global_def lid1 def in
              cont_of_option k uu____4175 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4205 = k_local_binding l in
                 cont_of_option Cont_fail uu____4205)
              (fun r  ->
                 let uu____4211 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4211)
              (fun uu____4215  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4223,uu____4224,uu____4225,l,uu____4227,uu____4228) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___90_4239  ->
               match uu___90_4239 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4242,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4254 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4260,uu____4261,uu____4262)
        -> FStar_Pervasives_Native.None
    | uu____4263 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4274 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4282 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4282
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4274 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4295 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4295 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___95_4325 =
            match uu___95_4325 with
            | (uu____4332,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4334) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4337 ->
                     let uu____4354 =
                       let uu____4355 =
                         let uu____4360 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4360, false) in
                       Term_name uu____4355 in
                     FStar_Pervasives_Native.Some uu____4354
                 | FStar_Syntax_Syntax.Sig_datacon uu____4361 ->
                     let uu____4376 =
                       let uu____4377 =
                         let uu____4382 =
                           let uu____4383 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4383 in
                         (uu____4382, false) in
                       Term_name uu____4377 in
                     FStar_Pervasives_Native.Some uu____4376
                 | FStar_Syntax_Syntax.Sig_let ((uu____4386,lbs),uu____4388)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4404 =
                       let uu____4405 =
                         let uu____4410 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4410, false) in
                       Term_name uu____4405 in
                     FStar_Pervasives_Native.Some uu____4404
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4412,uu____4413) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4417 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___91_4421  ->
                                  match uu___91_4421 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4422 -> false))) in
                     if uu____4417
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4427 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___92_4432  ->
                                      match uu___92_4432 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4433 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4438 -> true
                                      | uu____4439 -> false))) in
                         if uu____4427
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4442 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___93_4446  ->
                                   match uu___93_4446 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4447 -> false)) in
                         if uu____4442
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4449 =
                         FStar_Util.find_map quals
                           (fun uu___94_4454  ->
                              match uu___94_4454 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4458 -> FStar_Pervasives_Native.None) in
                       (match uu____4449 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4467 ->
                            let uu____4470 =
                              let uu____4471 =
                                let uu____4476 =
                                  let uu____4477 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4477 in
                                (uu____4476, false) in
                              Term_name uu____4471 in
                            FStar_Pervasives_Native.Some uu____4470)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4483 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4496 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4515 =
              let uu____4516 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4516 in
            FStar_Pervasives_Native.Some uu____4515 in
          let k_rec_binding uu____4532 =
            match uu____4532 with
            | (id1,l,dd) ->
                let uu____4544 =
                  let uu____4545 =
                    let uu____4550 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4550, false) in
                  Term_name uu____4545 in
                FStar_Pervasives_Native.Some uu____4544 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4556 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4556 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4574 -> FStar_Pervasives_Native.None)
            | uu____4581 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____4610 = try_lookup_name true exclude_interf env lid in
        match uu____4610 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4625 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4640 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4640 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4655 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4676 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4676 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4692;
             FStar_Syntax_Syntax.sigquals = uu____4693;
             FStar_Syntax_Syntax.sigmeta = uu____4694;
             FStar_Syntax_Syntax.sigattrs = uu____4695;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4714;
             FStar_Syntax_Syntax.sigquals = uu____4715;
             FStar_Syntax_Syntax.sigmeta = uu____4716;
             FStar_Syntax_Syntax.sigattrs = uu____4717;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4735,uu____4736,uu____4737,uu____4738,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4740;
             FStar_Syntax_Syntax.sigquals = uu____4741;
             FStar_Syntax_Syntax.sigmeta = uu____4742;
             FStar_Syntax_Syntax.sigattrs = uu____4743;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4765 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4786 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4786 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4796;
             FStar_Syntax_Syntax.sigquals = uu____4797;
             FStar_Syntax_Syntax.sigmeta = uu____4798;
             FStar_Syntax_Syntax.sigattrs = uu____4799;_},uu____4800)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4810;
             FStar_Syntax_Syntax.sigquals = uu____4811;
             FStar_Syntax_Syntax.sigmeta = uu____4812;
             FStar_Syntax_Syntax.sigattrs = uu____4813;_},uu____4814)
          -> FStar_Pervasives_Native.Some ne
      | uu____4823 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4836 = try_lookup_effect_name env lid in
      match uu____4836 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4839 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4848 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4848 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4858,uu____4859,uu____4860,uu____4861);
             FStar_Syntax_Syntax.sigrng = uu____4862;
             FStar_Syntax_Syntax.sigquals = uu____4863;
             FStar_Syntax_Syntax.sigmeta = uu____4864;
             FStar_Syntax_Syntax.sigattrs = uu____4865;_},uu____4866)
          ->
          let rec aux new_name =
            let uu____4885 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4885 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4903) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     FStar_Pervasives_Native.Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____4912,uu____4913,uu____4914,cmp,uu____4916) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4922 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4923,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4929 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___96_4958 =
        match uu___96_4958 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4967,uu____4968,uu____4969);
             FStar_Syntax_Syntax.sigrng = uu____4970;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4972;
             FStar_Syntax_Syntax.sigattrs = uu____4973;_},uu____4974)
            -> FStar_Pervasives_Native.Some quals
        | uu____4981 -> FStar_Pervasives_Native.None in
      let uu____4988 =
        resolve_in_open_namespaces' env lid
          (fun uu____4996  -> FStar_Pervasives_Native.None)
          (fun uu____5000  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4988 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5010 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____5027 =
        FStar_List.tryFind
          (fun uu____5042  ->
             match uu____5042 with
             | (mlid,modul) ->
                 let uu____5049 = FStar_Ident.path_of_lid mlid in
                 uu____5049 = path) env.modules in
      match uu____5027 with
      | FStar_Pervasives_Native.Some (uu____5056,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___97_5086 =
        match uu___97_5086 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5093,lbs),uu____5095);
             FStar_Syntax_Syntax.sigrng = uu____5096;
             FStar_Syntax_Syntax.sigquals = uu____5097;
             FStar_Syntax_Syntax.sigmeta = uu____5098;
             FStar_Syntax_Syntax.sigattrs = uu____5099;_},uu____5100)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5120 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5120
        | uu____5121 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5127  -> FStar_Pervasives_Native.None)
        (fun uu____5129  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___98_5152 =
        match uu___98_5152 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5162);
             FStar_Syntax_Syntax.sigrng = uu____5163;
             FStar_Syntax_Syntax.sigquals = uu____5164;
             FStar_Syntax_Syntax.sigmeta = uu____5165;
             FStar_Syntax_Syntax.sigattrs = uu____5166;_},uu____5167)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5190 -> FStar_Pervasives_Native.None)
        | uu____5197 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5207  -> FStar_Pervasives_Native.None)
        (fun uu____5211  -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let uu____5250 = try_lookup_name any_val exclude_interface env lid in
          match uu____5250 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5265 -> FStar_Pervasives_Native.None
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5292 = try_lookup_lid env l in
      match uu____5292 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5306) ->
          let uu____5311 =
            let uu____5312 = FStar_Syntax_Subst.compress e in
            uu____5312.FStar_Syntax_Syntax.n in
          (match uu____5311 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5318 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___119_5332 = env in
        {
          curmodule = (uu___119_5332.curmodule);
          curmonad = (uu___119_5332.curmonad);
          modules = (uu___119_5332.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___119_5332.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___119_5332.sigaccum);
          sigmap = (uu___119_5332.sigmap);
          iface = (uu___119_5332.iface);
          admitted_iface = (uu___119_5332.admitted_iface);
          expect_typ = (uu___119_5332.expect_typ);
          docs = (uu___119_5332.docs);
          remaining_iface_decls = (uu___119_5332.remaining_iface_decls);
          syntax_only = (uu___119_5332.syntax_only);
          ds_hooks = (uu___119_5332.ds_hooks)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_5361 =
        match uu___100_5361 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5368,uu____5369,uu____5370);
             FStar_Syntax_Syntax.sigrng = uu____5371;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5373;
             FStar_Syntax_Syntax.sigattrs = uu____5374;_},uu____5375)
            ->
            let uu____5380 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___99_5384  ->
                      match uu___99_5384 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5385 -> false)) in
            if uu____5380
            then
              let uu____5388 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5388
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5390;
             FStar_Syntax_Syntax.sigrng = uu____5391;
             FStar_Syntax_Syntax.sigquals = uu____5392;
             FStar_Syntax_Syntax.sigmeta = uu____5393;
             FStar_Syntax_Syntax.sigattrs = uu____5394;_},uu____5395)
            ->
            let uu____5414 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5414
        | uu____5415 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5421  -> FStar_Pervasives_Native.None)
        (fun uu____5423  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5448 =
        match uu___101_5448 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5457,uu____5458,uu____5459,uu____5460,datas,uu____5462);
             FStar_Syntax_Syntax.sigrng = uu____5463;
             FStar_Syntax_Syntax.sigquals = uu____5464;
             FStar_Syntax_Syntax.sigmeta = uu____5465;
             FStar_Syntax_Syntax.sigattrs = uu____5466;_},uu____5467)
            -> FStar_Pervasives_Native.Some datas
        | uu____5482 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5492  -> FStar_Pervasives_Native.None)
        (fun uu____5496  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5541 =
    let uu____5542 =
      let uu____5547 =
        let uu____5550 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5550 in
      let uu____5635 = FStar_ST.op_Bang record_cache in uu____5547 ::
        uu____5635 in
    FStar_ST.op_Colon_Equals record_cache uu____5542 in
  let pop1 uu____5801 =
    let uu____5802 =
      let uu____5807 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5807 in
    FStar_ST.op_Colon_Equals record_cache uu____5802 in
  let peek1 uu____5975 =
    let uu____5976 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5976 in
  let insert r =
    let uu____6065 =
      let uu____6070 = let uu____6073 = peek1 () in r :: uu____6073 in
      let uu____6076 =
        let uu____6081 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6081 in
      uu____6070 :: uu____6076 in
    FStar_ST.op_Colon_Equals record_cache uu____6065 in
  let filter1 uu____6249 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6258 =
      let uu____6263 =
        let uu____6268 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6268 in
      filtered :: uu____6263 in
    FStar_ST.op_Colon_Equals record_cache uu____6258 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6500 = record_cache_aux_with_filter in
  match uu____6500 with | (aux,uu____6544) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6587 = record_cache_aux_with_filter in
  match uu____6587 with | (uu____6614,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6658 = record_cache_aux in
  match uu____6658 with | (push1,uu____6680,uu____6681,uu____6682) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6705 = record_cache_aux in
  match uu____6705 with | (uu____6726,pop1,uu____6728,uu____6729) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6754 = record_cache_aux in
  match uu____6754 with | (uu____6777,uu____6778,peek1,uu____6780) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6803 = record_cache_aux in
  match uu____6803 with | (uu____6824,uu____6825,uu____6826,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6888) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___102_6904  ->
                   match uu___102_6904 with
                   | FStar_Syntax_Syntax.RecordType uu____6905 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6914 -> true
                   | uu____6923 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___103_6945  ->
                      match uu___103_6945 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6947,uu____6948,uu____6949,uu____6950,uu____6951);
                          FStar_Syntax_Syntax.sigrng = uu____6952;
                          FStar_Syntax_Syntax.sigquals = uu____6953;
                          FStar_Syntax_Syntax.sigmeta = uu____6954;
                          FStar_Syntax_Syntax.sigattrs = uu____6955;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6964 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___104_6999  ->
                    match uu___104_6999 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7003,uu____7004,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7006;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7008;
                        FStar_Syntax_Syntax.sigattrs = uu____7009;_} ->
                        let uu____7020 =
                          let uu____7021 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____7021 in
                        (match uu____7020 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7027,t,uu____7029,uu____7030,uu____7031);
                             FStar_Syntax_Syntax.sigrng = uu____7032;
                             FStar_Syntax_Syntax.sigquals = uu____7033;
                             FStar_Syntax_Syntax.sigmeta = uu____7034;
                             FStar_Syntax_Syntax.sigattrs = uu____7035;_} ->
                             let uu____7044 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____7044 with
                              | (formals,uu____7058) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7107  ->
                                            match uu____7107 with
                                            | (x,q) ->
                                                let uu____7120 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____7120
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7177  ->
                                            match uu____7177 with
                                            | (x,q) ->
                                                let uu____7190 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____7190,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
                                  let record =
                                    {
                                      typename;
                                      constrname =
                                        (constrname.FStar_Ident.ident);
                                      parms;
                                      fields;
                                      is_private_or_abstract =
                                        ((FStar_List.contains
                                            FStar_Syntax_Syntax.Private
                                            typename_quals)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              typename_quals));
                                      is_record = is_rec
                                    } in
                                  ((let uu____7205 =
                                      let uu____7208 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7208 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7205);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7369 =
                                            match uu____7369 with
                                            | (id1,uu____7377) ->
                                                let modul =
                                                  let uu____7383 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7383.FStar_Ident.str in
                                                let uu____7384 =
                                                  get_exported_id_set e modul in
                                                (match uu____7384 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7415 =
                                                         let uu____7416 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7416 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7415);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7560 =
                                                               let uu____7561
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____7561.FStar_Ident.ident in
                                                             uu____7560.FStar_Ident.idText in
                                                           let uu____7563 =
                                                             let uu____7564 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7564 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7563))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7717 -> ())
                    | uu____7718 -> ()))
        | uu____7719 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7734 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7734 with
        | (ns,id1) ->
            let uu____7751 = peek_record_cache () in
            FStar_Util.find_map uu____7751
              (fun record  ->
                 let uu____7757 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7763  -> FStar_Pervasives_Native.None)
                   uu____7757) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7765  -> Cont_ignore) (fun uu____7767  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7773 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7773)
        (fun k  -> fun uu____7779  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7790 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7790 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7796 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7808 = try_lookup_record_by_field_name env lid in
        match uu____7808 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7812 =
              let uu____7813 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7813 in
            let uu____7816 =
              let uu____7817 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7817 in
            uu____7812 = uu____7816 ->
            let uu____7820 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7824  -> Cont_ok ()) in
            (match uu____7820 with
             | Cont_ok uu____7825 -> true
             | uu____7826 -> false)
        | uu____7829 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7844 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7844 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7854 =
            let uu____7859 =
              let uu____7860 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7860
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7859, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7854
      | uu____7865 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7889  ->
    let uu____7890 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7890
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7914  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___105_7925  ->
      match uu___105_7925 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___106_7967 =
            match uu___106_7967 with
            | Rec_binding uu____7968 -> true
            | uu____7969 -> false in
          let this_env =
            let uu___120_7971 = env in
            let uu____7972 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___120_7971.curmodule);
              curmonad = (uu___120_7971.curmonad);
              modules = (uu___120_7971.modules);
              scope_mods = uu____7972;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___120_7971.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___120_7971.sigaccum);
              sigmap = (uu___120_7971.sigmap);
              iface = (uu___120_7971.iface);
              admitted_iface = (uu___120_7971.admitted_iface);
              expect_typ = (uu___120_7971.expect_typ);
              docs = (uu___120_7971.docs);
              remaining_iface_decls = (uu___120_7971.remaining_iface_decls);
              syntax_only = (uu___120_7971.syntax_only);
              ds_hooks = (uu___120_7971.ds_hooks)
            } in
          let uu____7975 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____7975 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7986 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___121_8001 = env in
      {
        curmodule = (uu___121_8001.curmodule);
        curmonad = (uu___121_8001.curmonad);
        modules = (uu___121_8001.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___121_8001.exported_ids);
        trans_exported_ids = (uu___121_8001.trans_exported_ids);
        includes = (uu___121_8001.includes);
        sigaccum = (uu___121_8001.sigaccum);
        sigmap = (uu___121_8001.sigmap);
        iface = (uu___121_8001.iface);
        admitted_iface = (uu___121_8001.admitted_iface);
        expect_typ = (uu___121_8001.expect_typ);
        docs = (uu___121_8001.docs);
        remaining_iface_decls = (uu___121_8001.remaining_iface_decls);
        syntax_only = (uu___121_8001.syntax_only);
        ds_hooks = (uu___121_8001.ds_hooks)
      }
let push_bv':
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true
let push_bv:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____8046 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____8046
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_DuplicateTopLevelNames,
              (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
            (FStar_Ident.range_of_lid l)
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8071) ->
              let uu____8076 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____8076 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____8084 =
          let uu____8089 =
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              (FStar_Ident.text_of_lid l) r in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8089) in
        FStar_Errors.raise_error uu____8084 (FStar_Ident.range_of_lid l) in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____8098 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8107 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8114 -> (false, true)
          | uu____8123 -> (false, false) in
        match uu____8098 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____8129 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8135 =
                     let uu____8136 = unique any_val exclude_interface env l in
                     Prims.op_Negation uu____8136 in
                   if uu____8135
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____8129 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8141 ->
                 (extract_record env globals s;
                  (let uu___122_8167 = env in
                   {
                     curmodule = (uu___122_8167.curmodule);
                     curmonad = (uu___122_8167.curmonad);
                     modules = (uu___122_8167.modules);
                     scope_mods = (uu___122_8167.scope_mods);
                     exported_ids = (uu___122_8167.exported_ids);
                     trans_exported_ids = (uu___122_8167.trans_exported_ids);
                     includes = (uu___122_8167.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___122_8167.sigmap);
                     iface = (uu___122_8167.iface);
                     admitted_iface = (uu___122_8167.admitted_iface);
                     expect_typ = (uu___122_8167.expect_typ);
                     docs = (uu___122_8167.docs);
                     remaining_iface_decls =
                       (uu___122_8167.remaining_iface_decls);
                     syntax_only = (uu___122_8167.syntax_only);
                     ds_hooks = (uu___122_8167.ds_hooks)
                   }))) in
      let env2 =
        let uu___123_8169 = env1 in
        let uu____8170 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___123_8169.curmodule);
          curmonad = (uu___123_8169.curmonad);
          modules = (uu___123_8169.modules);
          scope_mods = uu____8170;
          exported_ids = (uu___123_8169.exported_ids);
          trans_exported_ids = (uu___123_8169.trans_exported_ids);
          includes = (uu___123_8169.includes);
          sigaccum = (uu___123_8169.sigaccum);
          sigmap = (uu___123_8169.sigmap);
          iface = (uu___123_8169.iface);
          admitted_iface = (uu___123_8169.admitted_iface);
          expect_typ = (uu___123_8169.expect_typ);
          docs = (uu___123_8169.docs);
          remaining_iface_decls = (uu___123_8169.remaining_iface_decls);
          syntax_only = (uu___123_8169.syntax_only);
          ds_hooks = (uu___123_8169.ds_hooks)
        } in
      let uu____8247 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8273) ->
            let uu____8282 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8282)
        | uu____8309 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____8247 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8368  ->
                   match uu____8368 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8390 =
                                  let uu____8393 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8393 in
                                FStar_ST.op_Colon_Equals globals uu____8390);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8545 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8545.FStar_Ident.str in
                                    ((let uu____8547 =
                                        get_exported_id_set env3 modul in
                                      match uu____8547 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8577 =
                                            let uu____8578 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8578 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8577
                                      | FStar_Pervasives_Native.None  -> ());
                                     (match () with
                                      | () ->
                                          let is_iface =
                                            env3.iface &&
                                              (Prims.op_Negation
                                                 env3.admitted_iface) in
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___124_8731 = env3 in
              let uu____8732 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___124_8731.curmodule);
                curmonad = (uu___124_8731.curmonad);
                modules = (uu___124_8731.modules);
                scope_mods = uu____8732;
                exported_ids = (uu___124_8731.exported_ids);
                trans_exported_ids = (uu___124_8731.trans_exported_ids);
                includes = (uu___124_8731.includes);
                sigaccum = (uu___124_8731.sigaccum);
                sigmap = (uu___124_8731.sigmap);
                iface = (uu___124_8731.iface);
                admitted_iface = (uu___124_8731.admitted_iface);
                expect_typ = (uu___124_8731.expect_typ);
                docs = (uu___124_8731.docs);
                remaining_iface_decls = (uu___124_8731.remaining_iface_decls);
                syntax_only = (uu___124_8731.syntax_only);
                ds_hooks = (uu___124_8731.ds_hooks)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8815 =
        let uu____8820 = resolve_module_name env ns false in
        match uu____8820 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8834 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8848  ->
                      match uu____8848 with
                      | (m,uu____8854) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8834
            then (ns, Open_namespace)
            else
              (let uu____8860 =
                 let uu____8865 =
                   FStar_Util.format1 "Namespace %s cannot be found"
                     (FStar_Ident.text_of_lid ns) in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____8865) in
               FStar_Errors.raise_error uu____8860
                 (FStar_Ident.range_of_lid ns))
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8815 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8882 = resolve_module_name env ns false in
      match uu____8882 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8890 = current_module env1 in
              uu____8890.FStar_Ident.str in
            (let uu____8892 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8892 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8916 =
                   let uu____8919 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8919 in
                 FStar_ST.op_Colon_Equals incl uu____8916);
            (match () with
             | () ->
                 let uu____9070 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____9070 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9087 =
                          let uu____9104 = get_exported_id_set env1 curmod in
                          let uu____9111 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____9104, uu____9111) in
                        match uu____9087 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9165 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____9165 in
                              let ex = cur_exports k in
                              (let uu____9436 =
                                 let uu____9437 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9437 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9436);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9595 =
                                     let uu____9596 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9596 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9595) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9739 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9760 =
                        let uu____9765 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____9765) in
                      FStar_Errors.raise_error uu____9760
                        (FStar_Ident.range_of_lid ns1)))))
      | uu____9766 ->
          let uu____9769 =
            let uu____9774 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9774) in
          FStar_Errors.raise_error uu____9769 (FStar_Ident.range_of_lid ns)
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9784 = module_is_defined env l in
        if uu____9784
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9788 =
             let uu____9793 =
               FStar_Util.format1 "Module %s cannot be found"
                 (FStar_Ident.text_of_lid l) in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9793) in
           FStar_Errors.raise_error uu____9788 (FStar_Ident.range_of_lid l))
let push_doc:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____9809 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9809 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9813 =
                    let uu____9818 =
                      let uu____9819 = FStar_Ident.string_of_lid l in
                      let uu____9820 =
                        FStar_Parser_AST.string_of_fsdoc old_doc in
                      let uu____9821 = FStar_Parser_AST.string_of_fsdoc doc1 in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9819 uu____9820 uu____9821 in
                    (FStar_Errors.Warning_DocOverwrite, uu____9818) in
                  FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                    uu____9813);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9837 = try_lookup_lid env l in
                (match uu____9837 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9849 =
                         let uu____9850 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9850 in
                       if uu____9849
                       then
                         let uu____9851 =
                           let uu____9856 =
                             let uu____9857 =
                               FStar_Syntax_Print.lid_to_string l in
                             FStar_Util.format1
                               "Admitting %s without a definition" uu____9857 in
                           (FStar_Errors.Warning_AdmitWithoutDefinition,
                             uu____9856) in
                         FStar_Errors.log_issue (FStar_Ident.range_of_lid l)
                           uu____9851
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___125_9867 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___125_9867.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___125_9867.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___125_9867.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___125_9867.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9868 -> ())
            | uu____9877 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9894) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1  ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____9914,uu____9915,uu____9916,uu____9917,uu____9918)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____9931,uu____9932)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____9947 =
                                        let uu____9954 =
                                          let uu____9957 =
                                            let uu____9960 =
                                              let uu____9961 =
                                                let uu____9974 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ in
                                                (binders, uu____9974) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9961 in
                                            FStar_Syntax_Syntax.mk uu____9960 in
                                          uu____9957
                                            FStar_Pervasives_Native.None
                                            (FStar_Ident.range_of_lid lid) in
                                        (lid, univ_names, uu____9954) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____9947 in
                                    let se2 =
                                      let uu___126_9981 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___126_9981.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___126_9981.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___126_9981.FStar_Syntax_Syntax.sigattrs)
                                      } in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____9987 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9990,uu____9991) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9997,lbs),uu____9999) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____10020 =
                               let uu____10021 =
                                 let uu____10022 =
                                   let uu____10025 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____10025.FStar_Syntax_Syntax.fv_name in
                                 uu____10022.FStar_Syntax_Syntax.v in
                               uu____10021.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____10020))
                   else ();
                   if
                     (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                       &&
                       (Prims.op_Negation
                          (FStar_List.contains FStar_Syntax_Syntax.Private
                             quals))
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let lid =
                               let uu____10039 =
                                 let uu____10042 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____10042.FStar_Syntax_Syntax.fv_name in
                               uu____10039.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___127_10047 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___127_10047.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___127_10047.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___127_10047.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____10057 -> ()));
      (let curmod =
         let uu____10059 = current_module env in uu____10059.FStar_Ident.str in
       (let uu____10061 =
          let uu____10078 = get_exported_id_set env curmod in
          let uu____10085 = get_trans_exported_id_set env curmod in
          (uu____10078, uu____10085) in
        match uu____10061 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____10139 = cur_ex eikind in
                FStar_ST.op_Bang uu____10139 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____10409 =
                let uu____10410 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____10410 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10409 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10553 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___128_10571 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___128_10571.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___128_10571.exported_ids);
                    trans_exported_ids = (uu___128_10571.trans_exported_ids);
                    includes = (uu___128_10571.includes);
                    sigaccum = [];
                    sigmap = (uu___128_10571.sigmap);
                    iface = (uu___128_10571.iface);
                    admitted_iface = (uu___128_10571.admitted_iface);
                    expect_typ = (uu___128_10571.expect_typ);
                    docs = (uu___128_10571.docs);
                    remaining_iface_decls =
                      (uu___128_10571.remaining_iface_decls);
                    syntax_only = (uu___128_10571.syntax_only);
                    ds_hooks = (uu___128_10571.ds_hooks)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10598 =
       let uu____10601 = FStar_ST.op_Bang stack in env :: uu____10601 in
     FStar_ST.op_Colon_Equals stack uu____10598);
    (let uu___129_10708 = env in
     let uu____10709 = FStar_Util.smap_copy (sigmap env) in
     let uu____10720 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___129_10708.curmodule);
       curmonad = (uu___129_10708.curmonad);
       modules = (uu___129_10708.modules);
       scope_mods = (uu___129_10708.scope_mods);
       exported_ids = (uu___129_10708.exported_ids);
       trans_exported_ids = (uu___129_10708.trans_exported_ids);
       includes = (uu___129_10708.includes);
       sigaccum = (uu___129_10708.sigaccum);
       sigmap = uu____10709;
       iface = (uu___129_10708.iface);
       admitted_iface = (uu___129_10708.admitted_iface);
       expect_typ = (uu___129_10708.expect_typ);
       docs = uu____10720;
       remaining_iface_decls = (uu___129_10708.remaining_iface_decls);
       syntax_only = (uu___129_10708.syntax_only);
       ds_hooks = (uu___129_10708.ds_hooks)
     })
let pop: Prims.unit -> env =
  fun uu____10725  ->
    let uu____10726 = FStar_ST.op_Bang stack in
    match uu____10726 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10839 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10853 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10856 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10890 = FStar_Util.smap_try_find sm' k in
              match uu____10890 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___130_10915 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___130_10915.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___130_10915.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___130_10915.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___130_10915.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10916 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10921 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list;
  exported_id_fields: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkexported_ids__item__exported_id_terms:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
let __proj__Mkexported_ids__item__exported_id_fields:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
let as_exported_ids: exported_id_set -> exported_ids =
  fun e  ->
    let terms =
      let uu____11013 =
        let uu____11016 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____11016 in
      FStar_Util.set_elements uu____11013 in
    let fields =
      let uu____11275 =
        let uu____11278 = e Exported_id_field in FStar_ST.op_Bang uu____11278 in
      FStar_Util.set_elements uu____11275 in
    { exported_id_terms = terms; exported_id_fields = fields }
let as_exported_id_set:
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____11570 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11570 in
        let fields =
          let uu____11580 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11580 in
        (fun uu___107_11585  ->
           match uu___107_11585 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option;}
[@@deriving show]
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_includes:
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
let default_mii: module_inclusion_info =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes:
  'Auu____11705 .
    'Auu____11705 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11705 Prims.list FStar_ST.ref
  =
  fun uu___108_11717  ->
    match uu___108_11717 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11750 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11750 as_exported_ids in
      let uu____11753 = as_ids_opt env.exported_ids in
      let uu____11756 = as_ids_opt env.trans_exported_ids in
      let uu____11759 =
        let uu____11764 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11764 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11753;
        mii_trans_exported_ids = uu____11756;
        mii_includes = uu____11759
      }
let prepare_module_or_interface:
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___109_11913 =
                  match uu___109_11913 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11925  ->
                     match uu____11925 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11949 =
                    let uu____11954 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11954, Open_namespace) in
                  [uu____11949]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____11984 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11984);
              (match () with
               | () ->
                   ((let uu____12008 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____12008);
                    (match () with
                     | () ->
                         ((let uu____12032 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____12032);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___131_12064 = env1 in
                                 let uu____12065 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___131_12064.curmonad);
                                   modules = (uu___131_12064.modules);
                                   scope_mods = uu____12065;
                                   exported_ids =
                                     (uu___131_12064.exported_ids);
                                   trans_exported_ids =
                                     (uu___131_12064.trans_exported_ids);
                                   includes = (uu___131_12064.includes);
                                   sigaccum = (uu___131_12064.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___131_12064.expect_typ);
                                   docs = (uu___131_12064.docs);
                                   remaining_iface_decls =
                                     (uu___131_12064.remaining_iface_decls);
                                   syntax_only = (uu___131_12064.syntax_only);
                                   ds_hooks = (uu___131_12064.ds_hooks)
                                 } in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____12077 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____12103  ->
                      match uu____12103 with
                      | (l,uu____12109) -> FStar_Ident.lid_equals l mname)) in
            match uu____12077 with
            | FStar_Pervasives_Native.None  ->
                let uu____12118 = prep env in (uu____12118, false)
            | FStar_Pervasives_Native.Some (uu____12119,m) ->
                ((let uu____12126 =
                    (let uu____12129 = FStar_Options.interactive () in
                     Prims.op_Negation uu____12129) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____12126
                  then
                    let uu____12130 =
                      let uu____12135 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____12135) in
                    FStar_Errors.raise_error uu____12130
                      (FStar_Ident.range_of_lid mname)
                  else ());
                 (let uu____12137 =
                    let uu____12138 = push env in prep uu____12138 in
                  (uu____12137, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.strcat "Trying to define monad "
                 (Prims.strcat mname.FStar_Ident.idText
                    (Prims.strcat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None  ->
          let uu___132_12146 = env in
          {
            curmodule = (uu___132_12146.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___132_12146.modules);
            scope_mods = (uu___132_12146.scope_mods);
            exported_ids = (uu___132_12146.exported_ids);
            trans_exported_ids = (uu___132_12146.trans_exported_ids);
            includes = (uu___132_12146.includes);
            sigaccum = (uu___132_12146.sigaccum);
            sigmap = (uu___132_12146.sigmap);
            iface = (uu___132_12146.iface);
            admitted_iface = (uu___132_12146.admitted_iface);
            expect_typ = (uu___132_12146.expect_typ);
            docs = (uu___132_12146.docs);
            remaining_iface_decls = (uu___132_12146.remaining_iface_decls);
            syntax_only = (uu___132_12146.syntax_only);
            ds_hooks = (uu___132_12146.ds_hooks)
          }
let fail_or:
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup  ->
      fun lid  ->
        let uu____12173 = lookup lid in
        match uu____12173 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____12186  ->
                   match uu____12186 with
                   | (lid1,uu____12192) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              FStar_Util.format1 "Identifier not found: [%s]"
                (FStar_Ident.text_of_lid lid) in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____12197 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____12197
                     (FStar_Ident.range_of_lid lid) in
                 let uu____12198 = resolve_module_name env modul true in
                 match uu____12198 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m  -> m = modul'.FStar_Ident.str)
                          opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText) in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1)
              (FStar_Ident.range_of_lid lid)
        | FStar_Pervasives_Native.Some r -> r
let fail_or2:
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id1  ->
      let uu____12229 = lookup id1 in
      match uu____12229 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r