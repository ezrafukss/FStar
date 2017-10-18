open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app:
  'Auu____20 'Auu____21 .
    Prims.bool -> ('Auu____21 -> 'Auu____20) -> 'Auu____21 -> 'Auu____20
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
let should_unparen: Prims.bool FStar_ST.ref = FStar_Util.mk_ref true
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____194 =
      let uu____195 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____195 in
    if uu____194
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____244 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____259 'Auu____260 .
    'Auu____260 ->
      ('Auu____259 -> 'Auu____260) ->
        'Auu____259 FStar_Pervasives_Native.option -> 'Auu____260
  =
  fun n1  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
let prefix2:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
let op_Hat_Slash_Plus_Hat:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body
let jump2: FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
let infix2:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1")
let infix0:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1")
let break1: FStar_Pprint.document = FStar_Pprint.break_ (Prims.parse_int "1")
let separate_break_map:
  'Auu____329 .
    FStar_Pprint.document ->
      ('Auu____329 -> FStar_Pprint.document) ->
        'Auu____329 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____351 =
          let uu____352 =
            let uu____353 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____353 in
          FStar_Pprint.separate_map uu____352 f l in
        FStar_Pprint.group uu____351
let precede_break_separate_map:
  'Auu____364 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____364 -> FStar_Pprint.document) ->
          'Auu____364 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____390 =
            let uu____391 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____392 =
              let uu____393 = FStar_List.hd l in
              FStar_All.pipe_right uu____393 f in
            FStar_Pprint.precede uu____391 uu____392 in
          let uu____394 =
            let uu____395 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____401 =
                   let uu____402 =
                     let uu____403 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____403 in
                   FStar_Pprint.op_Hat_Hat sep uu____402 in
                 FStar_Pprint.op_Hat_Hat break1 uu____401) uu____395 in
          FStar_Pprint.op_Hat_Hat uu____390 uu____394
let concat_break_map:
  'Auu____410 .
    ('Auu____410 -> FStar_Pprint.document) ->
      'Auu____410 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____428 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____432 = f x in FStar_Pprint.op_Hat_Hat uu____432 break1)
          l in
      FStar_Pprint.group uu____428
let parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let soft_parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let soft_braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let brackets_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_brackets_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_begin_end_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____461 = str "begin" in
    let uu____462 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____461 contents uu____462
let separate_map_or_flow:
  'Auu____471 .
    FStar_Pprint.document ->
      ('Auu____471 -> FStar_Pprint.document) ->
        'Auu____471 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
  'Auu____512 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____512 -> FStar_Pprint.document) ->
                  'Auu____512 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____557 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____557
                       closing)
let soft_surround_map_or_flow:
  'Auu____576 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____576 -> FStar_Pprint.document) ->
                  'Auu____576 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____621 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____621
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____635  ->
    match uu____635 with
    | (comment,keywords) ->
        let uu____660 =
          let uu____661 =
            let uu____664 = str comment in
            let uu____665 =
              let uu____668 =
                let uu____671 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____680  ->
                       match uu____680 with
                       | (k,v1) ->
                           let uu____687 =
                             let uu____690 = str k in
                             let uu____691 =
                               let uu____694 =
                                 let uu____697 = str v1 in [uu____697] in
                               FStar_Pprint.rarrow :: uu____694 in
                             uu____690 :: uu____691 in
                           FStar_Pprint.concat uu____687) keywords in
                [uu____671] in
              FStar_Pprint.space :: uu____668 in
            uu____664 :: uu____665 in
          FStar_Pprint.concat uu____661 in
        FStar_Pprint.group uu____660
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____702 =
      let uu____703 = unparen e in uu____703.FStar_Parser_AST.tm in
    match uu____702 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____704 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____713 =
        let uu____714 = unparen t in uu____714.FStar_Parser_AST.tm in
      match uu____713 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____716 -> false
let is_tuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_tuple_data_lid'
let is_dtuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_dtuple_data_lid'
let is_list_structure:
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        let uu____738 =
          let uu____739 = unparen e in uu____739.FStar_Parser_AST.tm in
        match uu____738 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____752::(e2,uu____754)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____777 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____790 =
      let uu____791 = unparen e in uu____791.FStar_Parser_AST.tm in
    match uu____790 with
    | FStar_Parser_AST.Construct (uu____794,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____805,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____826 = extract_from_list e2 in e1 :: uu____826
    | uu____829 ->
        let uu____830 =
          let uu____831 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____831 in
        failwith uu____830
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____838 =
      let uu____839 = unparen e in uu____839.FStar_Parser_AST.tm in
    match uu____838 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____841;
           FStar_Parser_AST.level = uu____842;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____844 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____849 =
      let uu____850 = unparen e in uu____850.FStar_Parser_AST.tm in
    match uu____849 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____853;
           FStar_Parser_AST.level = uu____854;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____856;
                                                        FStar_Parser_AST.level
                                                          = uu____857;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____859;
                                                   FStar_Parser_AST.level =
                                                     uu____860;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.set_singleton)
          &&
          (FStar_Ident.lid_equals maybe_addr_of_lid
             FStar_Parser_Const.heap_addr_of_lid)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____862;
                FStar_Parser_AST.level = uu____863;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____865;
           FStar_Parser_AST.level = uu____866;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____868 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____875 =
      let uu____876 = unparen e in uu____876.FStar_Parser_AST.tm in
    match uu____875 with
    | FStar_Parser_AST.Var uu____879 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____880;
           FStar_Parser_AST.range = uu____881;
           FStar_Parser_AST.level = uu____882;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____883;
                                                        FStar_Parser_AST.range
                                                          = uu____884;
                                                        FStar_Parser_AST.level
                                                          = uu____885;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____887;
                                                   FStar_Parser_AST.level =
                                                     uu____888;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____889;
                FStar_Parser_AST.range = uu____890;
                FStar_Parser_AST.level = uu____891;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____893;
           FStar_Parser_AST.level = uu____894;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____896 = extract_from_ref_set e1 in
        let uu____899 = extract_from_ref_set e2 in
        FStar_List.append uu____896 uu____899
    | uu____902 ->
        let uu____903 =
          let uu____904 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____904 in
        failwith uu____903
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____911 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____911
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____916 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____916
let is_general_prefix_op: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0") in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) && ((FStar_Ident.text_of_id op) <> "~"))
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____965 =
        let uu____966 = unparen e1 in uu____966.FStar_Parser_AST.tm in
      match uu____965 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____984 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____999 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1004 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1009 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___99_1027  ->
    match uu___99_1027 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___100_1045  ->
      match uu___100_1045 with
      | FStar_Util.Inl c ->
          let uu____1051 = FStar_String.get s (Prims.parse_int "0") in
          uu____1051 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____1059 .
    Prims.string ->
      ('Auu____1059,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1077  ->
      match uu____1077 with
      | (assoc_levels,tokens) ->
          let uu____1102 = FStar_List.tryFind (matches_token s) tokens in
          uu____1102 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1125 .
    Prims.unit ->
      (associativity,('Auu____1125,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1136  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1153 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1153) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1164  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1189 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1189) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1200  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1221 .
    Prims.unit ->
      (associativity,('Auu____1221,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1232  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1249 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1249) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1260  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1281 .
    Prims.unit ->
      (associativity,('Auu____1281,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1292  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1309 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1309) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1320  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1337 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1337) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1348  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1373 .
    Prims.unit ->
      (associativity,('Auu____1373,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1384  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1401 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1401) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1412  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1429 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1429) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1440  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1457 .
    Prims.unit ->
      (associativity,('Auu____1457,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1468  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1485 .
    Prims.unit ->
      (associativity,('Auu____1485,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1496  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1513 .
    Prims.unit ->
      (associativity,('Auu____1513,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1524  -> (Right, [FStar_Util.Inr "::"])
let level_associativity_spec:
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  [opinfix4 ();
  opinfix3 ();
  opinfix2 ();
  opinfix1 ();
  pipe_right ();
  opinfix0d ();
  opinfix0c ();
  opinfix0b ();
  opinfix0a ();
  colon_equals ();
  amp ();
  colon_colon ()]
let level_table:
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  let levels_from_associativity l uu___101_1711 =
    match uu___101_1711 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1749  ->
         match uu____1749 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1826 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1826 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1874) ->
          assoc_levels
      | uu____1915 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1953 .
    ('Auu____1953,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2009 =
        FStar_List.tryFind
          (fun uu____2047  ->
             match uu____2047 with
             | (uu____2064,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____2009 with
      | FStar_Pervasives_Native.Some ((uu____2102,l1,uu____2104),uu____2105)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2156 =
            let uu____2157 =
              let uu____2158 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2158 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2157 in
          failwith uu____2156 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2192 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2192) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2205  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2280 =
      let uu____2293 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2293 (operatorInfix0ad12 ()) in
    uu____2280 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2397 =
      let uu____2410 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2410 opinfix34 in
    uu____2397 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2472 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2472
    then Prims.parse_int "1"
    else
      (let uu____2474 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2474
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2483 . FStar_Ident.ident -> 'Auu____2483 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_28 when _0_28 = (Prims.parse_int "0") -> true
      | _0_29 when _0_29 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
      | _0_30 when _0_30 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (FStar_List.mem (FStar_Ident.text_of_id op)
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_31 when _0_31 = (Prims.parse_int "3") ->
          FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
      | uu____2496 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2530 .
    ('Auu____2530 -> FStar_Pprint.document) ->
      'Auu____2530 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2562 = FStar_ST.op_Bang comment_stack in
          match uu____2562 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2648 = FStar_Range.range_before_pos crange print_pos in
              if uu____2648
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2712 =
                    let uu____2713 =
                      let uu____2714 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2714
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2713 in
                  comments_before_pos uu____2712 print_pos lookahead_pos))
              else
                (let uu____2716 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2716)) in
        let uu____2717 =
          let uu____2722 =
            let uu____2723 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2723 in
          let uu____2724 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2722 uu____2724 in
        match uu____2717 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2730 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2730
              else comments in
            let uu____2736 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2736
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2753 = FStar_ST.op_Bang comment_stack in
          match uu____2753 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2891 =
                    let uu____2892 =
                      let uu____2893 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2893 in
                    uu____2892 - lbegin in
                  max k uu____2891 in
                let doc2 =
                  let uu____2895 =
                    let uu____2896 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2897 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2896 uu____2897 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2895 in
                let uu____2898 =
                  let uu____2899 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2899 in
                place_comments_until_pos (Prims.parse_int "1") uu____2898
                  pos_end doc2))
          | uu____2900 ->
              let lnum =
                let uu____2908 =
                  let uu____2909 = FStar_Range.line_of_pos pos_end in
                  uu____2909 - lbegin in
                max (Prims.parse_int "1") uu____2908 in
              let uu____2910 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2910
let separate_map_with_comments:
  'Auu____2923 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2923 -> FStar_Pprint.document) ->
          'Auu____2923 Prims.list ->
            ('Auu____2923 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2971 x =
              match uu____2971 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2985 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2985 doc1 in
                  let uu____2986 =
                    let uu____2987 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2987 in
                  let uu____2988 =
                    let uu____2989 =
                      let uu____2990 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2990 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2989 in
                  (uu____2986, uu____2988) in
            let uu____2991 =
              let uu____2998 = FStar_List.hd xs in
              let uu____2999 = FStar_List.tl xs in (uu____2998, uu____2999) in
            match uu____2991 with
            | (x,xs1) ->
                let init1 =
                  let uu____3015 =
                    let uu____3016 =
                      let uu____3017 = extract_range x in
                      FStar_Range.end_of_range uu____3017 in
                    FStar_Range.line_of_pos uu____3016 in
                  let uu____3018 =
                    let uu____3019 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3019 in
                  (uu____3015, uu____3018) in
                let uu____3020 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____3020
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3322 =
      let uu____3323 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3324 =
        let uu____3325 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3326 =
          let uu____3327 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3328 =
            let uu____3329 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3329 in
          FStar_Pprint.op_Hat_Hat uu____3327 uu____3328 in
        FStar_Pprint.op_Hat_Hat uu____3325 uu____3326 in
      FStar_Pprint.op_Hat_Hat uu____3323 uu____3324 in
    FStar_Pprint.group uu____3322
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3332 =
      let uu____3333 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3333 in
    let uu____3334 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3332 FStar_Pprint.space uu____3334
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3335  ->
    match uu____3335 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3369 =
                match uu____3369 with
                | (kwd,arg) ->
                    let uu____3376 = str "@" in
                    let uu____3377 =
                      let uu____3378 = str kwd in
                      let uu____3379 =
                        let uu____3380 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3380 in
                      FStar_Pprint.op_Hat_Hat uu____3378 uu____3379 in
                    FStar_Pprint.op_Hat_Hat uu____3376 uu____3377 in
              let uu____3381 =
                let uu____3382 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3382 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3381 in
        let uu____3387 =
          let uu____3388 =
            let uu____3389 =
              let uu____3390 =
                let uu____3391 = str doc1 in
                let uu____3392 =
                  let uu____3393 =
                    let uu____3394 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3394 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3393 in
                FStar_Pprint.op_Hat_Hat uu____3391 uu____3392 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3390 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3389 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3388 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3387
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3398 =
          let uu____3399 = str "val" in
          let uu____3400 =
            let uu____3401 =
              let uu____3402 = p_lident lid in
              let uu____3403 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3402 uu____3403 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3401 in
          FStar_Pprint.op_Hat_Hat uu____3399 uu____3400 in
        let uu____3404 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3398 uu____3404
    | FStar_Parser_AST.TopLevelLet (uu____3405,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3430 =
               let uu____3431 = str "let" in
               let uu____3432 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3431 uu____3432 in
             FStar_Pprint.group uu____3430) lbs
    | uu____3433 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3436 =
          let uu____3437 = str "open" in
          let uu____3438 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3437 uu____3438 in
        FStar_Pprint.group uu____3436
    | FStar_Parser_AST.Include uid ->
        let uu____3440 =
          let uu____3441 = str "include" in
          let uu____3442 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3441 uu____3442 in
        FStar_Pprint.group uu____3440
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3445 =
          let uu____3446 = str "module" in
          let uu____3447 =
            let uu____3448 =
              let uu____3449 = p_uident uid1 in
              let uu____3450 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3449 uu____3450 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3448 in
          FStar_Pprint.op_Hat_Hat uu____3446 uu____3447 in
        let uu____3451 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3445 uu____3451
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3453 =
          let uu____3454 = str "module" in
          let uu____3455 =
            let uu____3456 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3456 in
          FStar_Pprint.op_Hat_Hat uu____3454 uu____3455 in
        FStar_Pprint.group uu____3453
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3489 = str "effect" in
          let uu____3490 =
            let uu____3491 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3491 in
          FStar_Pprint.op_Hat_Hat uu____3489 uu____3490 in
        let uu____3492 =
          let uu____3493 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3493 FStar_Pprint.equals in
        let uu____3494 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3492 uu____3494
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3512 = str "type" in
        let uu____3513 = str "and" in
        precede_break_separate_map uu____3512 uu____3513 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3535 = str "let" in
          let uu____3536 =
            let uu____3537 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3537 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3535 uu____3536 in
        let uu____3538 =
          let uu____3539 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3539 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3538 p_letbinding lbs
          (fun uu____3547  ->
             match uu____3547 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3556 =
          let uu____3557 = str "val" in
          let uu____3558 =
            let uu____3559 =
              let uu____3560 = p_lident lid in
              let uu____3561 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3560 uu____3561 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3559 in
          FStar_Pprint.op_Hat_Hat uu____3557 uu____3558 in
        let uu____3562 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3556 uu____3562
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3566 =
            let uu____3567 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3567 FStar_Util.is_upper in
          if uu____3566
          then FStar_Pprint.empty
          else
            (let uu____3569 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3569 FStar_Pprint.space) in
        let uu____3570 =
          let uu____3571 =
            let uu____3572 = p_ident id in
            let uu____3573 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3572 uu____3573 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3571 in
        let uu____3574 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3570 uu____3574
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3581 = str "exception" in
        let uu____3582 =
          let uu____3583 =
            let uu____3584 = p_uident uid in
            let uu____3585 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3590 = str "of" in
                   let uu____3591 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3590 uu____3591) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3584 uu____3585 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3583 in
        FStar_Pprint.op_Hat_Hat uu____3581 uu____3582
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3593 = str "new_effect" in
        let uu____3594 =
          let uu____3595 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3595 in
        FStar_Pprint.op_Hat_Hat uu____3593 uu____3594
    | FStar_Parser_AST.SubEffect se ->
        let uu____3597 = str "sub_effect" in
        let uu____3598 =
          let uu____3599 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3599 in
        FStar_Pprint.op_Hat_Hat uu____3597 uu____3598
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3602 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3602 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3603 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3604) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___102_3614  ->
    match uu___102_3614 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3623 = str "#set-options" in
        let uu____3624 =
          let uu____3625 =
            let uu____3626 = str s in FStar_Pprint.dquotes uu____3626 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3625 in
        FStar_Pprint.op_Hat_Hat uu____3623 uu____3624
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3630 = str "#reset-options" in
        let uu____3631 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3635 =
                 let uu____3636 = str s in FStar_Pprint.dquotes uu____3636 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3635) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3630 uu____3631
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3687  ->
    match uu____3687 with
    | (typedecl,fsdoc_opt) ->
        let uu____3700 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3701 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3700 uu____3701
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___103_3695  ->
    match uu___103_3695 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3717 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3733 =
          let uu____3734 = p_typ t in prefix2 FStar_Pprint.equals uu____3734 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3778 =
          match uu____3778 with
          | (lid1,t,doc_opt) ->
              let uu____3794 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3794 in
        let p_fields uu____3808 =
          let uu____3809 =
            let uu____3810 =
              let uu____3811 =
                let uu____3812 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3812 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3811 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3810 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3809 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3876 =
          match uu____3876 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3902 =
                  let uu____3903 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3903 in
                FStar_Range.extend_to_end_of_line uu____3902 in
              let p_constructorBranch decl =
                let uu____3936 =
                  let uu____3937 =
                    let uu____3938 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3938 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3937 in
                FStar_Pprint.group uu____3936 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3958 =
          let uu____3959 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3959 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3974  ->
             let uu____3975 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3975)
and p_typeDeclPrefix:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____3990 = p_ident lid in
            let uu____3991 =
              let uu____3992 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3992 in
            FStar_Pprint.op_Hat_Hat uu____3990 uu____3991
          else
            (let binders_doc =
               let uu____3995 = p_typars bs in
               let uu____3996 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4000 =
                        let uu____4001 =
                          let uu____4002 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4002 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4001 in
                      FStar_Pprint.op_Hat_Hat break1 uu____4000) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3995 uu____3996 in
             let uu____4003 = p_ident lid in
             let uu____4004 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4003 binders_doc uu____4004)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4005  ->
    match uu____4005 with
    | (lid,t,doc_opt) ->
        let uu____4021 =
          let uu____4022 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____4023 =
            let uu____4024 = p_lident lid in
            let uu____4025 =
              let uu____4026 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4026 in
            FStar_Pprint.op_Hat_Hat uu____4024 uu____4025 in
          FStar_Pprint.op_Hat_Hat uu____4022 uu____4023 in
        FStar_Pprint.group uu____4021
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____4027  ->
    match uu____4027 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____4055 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____4056 =
          let uu____4057 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____4058 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4063 =
                   let uu____4064 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4064 in
                 let uu____4065 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____4063 uu____4065) t_opt in
          FStar_Pprint.op_Hat_Hat uu____4057 uu____4058 in
        FStar_Pprint.op_Hat_Hat uu____4055 uu____4056
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4066  ->
    match uu____4066 with
    | (pat,uu____4072) ->
        let uu____4073 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4084 =
                let uu____4085 =
                  let uu____4086 =
                    let uu____4087 =
                      let uu____4088 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4088 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4087 in
                  FStar_Pprint.group uu____4086 in
                FStar_Pprint.op_Hat_Hat break1 uu____4085 in
              (pat1, uu____4084)
          | uu____4089 -> (pat, FStar_Pprint.empty) in
        (match uu____4073 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4093);
                     FStar_Parser_AST.prange = uu____4094;_},pats)
                  ->
                  let uu____4104 =
                    let uu____4105 = p_lident x in
                    let uu____4106 =
                      let uu____4107 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____4107 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4105 uu____4106 in
                  FStar_Pprint.group uu____4104
              | uu____4108 ->
                  let uu____4109 =
                    let uu____4110 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____4110 ascr_doc in
                  FStar_Pprint.group uu____4109))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4111  ->
    match uu____4111 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____4119 =
          let uu____4120 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____4120 in
        let uu____4121 = p_term e in prefix2 uu____4119 uu____4121
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___104_4115  ->
    match uu___104_4115 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls
and p_effectRedefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____4147 = p_uident uid in
        let uu____4148 = p_binders true bs in
        let uu____4149 =
          let uu____4150 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____4150 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4147 uu____4148 uu____4149
and p_effectDefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let uu____4159 =
            let uu____4160 =
              let uu____4161 =
                let uu____4162 = p_uident uid in
                let uu____4163 = p_binders true bs in
                let uu____4164 =
                  let uu____4165 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____4165 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4162 uu____4163 uu____4164 in
              FStar_Pprint.group uu____4161 in
            let uu____4166 =
              let uu____4167 = str "with" in
              let uu____4168 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____4167 uu____4168 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4160 uu____4166 in
          braces_with_nesting uu____4159
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4198 =
          let uu____4199 = p_lident lid in
          let uu____4200 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____4199 uu____4200 in
        let uu____4201 = p_simpleTerm e in prefix2 uu____4198 uu____4201
    | uu____4202 ->
        let uu____4203 =
          let uu____4204 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4204 in
        failwith uu____4203
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4259 =
        match uu____4259 with
        | (kwd,t) ->
            let uu____4266 =
              let uu____4267 = str kwd in
              let uu____4268 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4267 uu____4268 in
            let uu____4269 = p_simpleTerm t in prefix2 uu____4266 uu____4269 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4274 =
      let uu____4275 =
        let uu____4276 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4277 =
          let uu____4278 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4278 in
        FStar_Pprint.op_Hat_Hat uu____4276 uu____4277 in
      let uu____4279 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4275 uu____4279 in
    let uu____4280 =
      let uu____4281 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4281 in
    FStar_Pprint.op_Hat_Hat uu____4274 uu____4280
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___105_4275  ->
    match uu___105_4275 with
    | FStar_Parser_AST.Private  -> str "private"
    | FStar_Parser_AST.Abstract  -> str "abstract"
    | FStar_Parser_AST.Noeq  -> str "noeq"
    | FStar_Parser_AST.Unopteq  -> str "unopteq"
    | FStar_Parser_AST.Assumption  -> str "assume"
    | FStar_Parser_AST.DefaultEffect  -> str "default"
    | FStar_Parser_AST.TotalEffect  -> str "total"
    | FStar_Parser_AST.Effect_qual  -> FStar_Pprint.empty
    | FStar_Parser_AST.New  -> str "new"
    | FStar_Parser_AST.Inline  -> str "inline"
    | FStar_Parser_AST.Visible  -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen  -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction  -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible  -> str "irreducible"
    | FStar_Parser_AST.NoExtract  -> str "noextract"
    | FStar_Parser_AST.Reifiable  -> str "reifiable"
    | FStar_Parser_AST.Reflectable  -> str "reflectable"
    | FStar_Parser_AST.Opaque  -> str "opaque"
    | FStar_Parser_AST.Logic  -> str "logic"
and p_qualifiers: FStar_Parser_AST.qualifiers -> FStar_Pprint.document =
  fun qs  ->
    let uu____4284 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4284
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___106_4278  ->
    match uu___106_4278 with
    | FStar_Parser_AST.Rec  ->
        let uu____4286 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4286
    | FStar_Parser_AST.Mutable  ->
        let uu____4287 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4287
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___107_4281  ->
    match uu___107_4281 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4293 =
          let uu____4294 =
            let uu____4295 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4295 in
          FStar_Pprint.separate_map uu____4294 p_tuplePattern pats in
        FStar_Pprint.group uu____4293
    | uu____4296 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4303 =
          let uu____4304 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4304 p_constructorPattern pats in
        FStar_Pprint.group uu____4303
    | uu____4305 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4308;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4313 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4314 = p_constructorPattern hd1 in
        let uu____4315 = p_constructorPattern tl1 in
        infix0 uu____4313 uu____4314 uu____4315
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4317;_},pats)
        ->
        let uu____4323 = p_quident uid in
        let uu____4324 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4323 uu____4324
    | uu____4325 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4329 =
          let uu____4334 =
            let uu____4335 = unparen t in uu____4335.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4334) in
        (match uu____4329 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4340;
               FStar_Parser_AST.blevel = uu____4341;
               FStar_Parser_AST.aqual = uu____4342;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4348 =
               let uu____4349 = p_ident lid in
               p_refinement aqual uu____4349 t1 phi in
             soft_parens_with_nesting uu____4348
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4351;
               FStar_Parser_AST.blevel = uu____4352;
               FStar_Parser_AST.aqual = uu____4353;_},phi))
             ->
             let uu____4355 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4355
         | uu____4356 ->
             let uu____4361 =
               let uu____4362 = p_tuplePattern pat in
               let uu____4363 =
                 let uu____4364 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4365 =
                   let uu____4366 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4366 in
                 FStar_Pprint.op_Hat_Hat uu____4364 uu____4365 in
               FStar_Pprint.op_Hat_Hat uu____4362 uu____4363 in
             soft_parens_with_nesting uu____4361)
    | FStar_Parser_AST.PatList pats ->
        let uu____4370 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4370 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatVector pats ->
        let uu____4374 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____4375 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        let uu____4376 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____4374 uu____4375 uu____4376
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4391 =
          match uu____4391 with
          | (lid,pat) ->
              let uu____4398 = p_qlident lid in
              let uu____4399 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4398 uu____4399 in
        let uu____4400 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4400
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4410 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4411 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4412 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4410 uu____4411 uu____4412
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4423 =
          let uu____4424 =
            let uu____4425 = str (FStar_Ident.text_of_id op) in
            let uu____4426 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4425 uu____4426 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4424 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4423
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4434 = FStar_Pprint.optional p_aqual aqual in
        let uu____4435 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4434 uu____4435
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4437 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4440;
           FStar_Parser_AST.prange = uu____4441;_},uu____4442)
        ->
        let uu____4447 = p_tuplePattern p in
        soft_parens_with_nesting uu____4447
    | FStar_Parser_AST.PatTuple (uu____4448,false ) ->
        let uu____4453 = p_tuplePattern p in
        soft_parens_with_nesting uu____4453
    | uu____4454 ->
        let uu____4455 =
          let uu____4456 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4456 in
        failwith uu____4455
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4460 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4461 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4460 uu____4461
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4466 =
              let uu____4467 = unparen t in uu____4467.FStar_Parser_AST.tm in
            match uu____4466 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4470;
                   FStar_Parser_AST.blevel = uu____4471;
                   FStar_Parser_AST.aqual = uu____4472;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4474 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4474 t1 phi
            | uu____4475 ->
                let uu____4476 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4477 =
                  let uu____4478 = p_lident lid in
                  let uu____4479 =
                    let uu____4480 =
                      let uu____4481 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4482 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4481 uu____4482 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4480 in
                  FStar_Pprint.op_Hat_Hat uu____4478 uu____4479 in
                FStar_Pprint.op_Hat_Hat uu____4476 uu____4477 in
          if is_atomic
          then
            let uu____4483 =
              let uu____4484 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4484 in
            FStar_Pprint.group uu____4483
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4486 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4492 =
            let uu____4493 = unparen t in uu____4493.FStar_Parser_AST.tm in
          (match uu____4492 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4495;
                  FStar_Parser_AST.blevel = uu____4496;
                  FStar_Parser_AST.aqual = uu____4497;_},phi)
               ->
               if is_atomic
               then
                 let uu____4499 =
                   let uu____4500 =
                     let uu____4501 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4501 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4500 in
                 FStar_Pprint.group uu____4499
               else
                 (let uu____4503 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4503)
           | uu____4504 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4512 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4513 =
            let uu____4514 =
              let uu____4515 =
                let uu____4516 = p_appTerm t in
                let uu____4517 =
                  let uu____4518 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4518 in
                FStar_Pprint.op_Hat_Hat uu____4516 uu____4517 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4515 in
            FStar_Pprint.op_Hat_Hat binder uu____4514 in
          FStar_Pprint.op_Hat_Hat uu____4512 uu____4513
and p_binders:
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs
and p_qlident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_quident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_ident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_uident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_tvar: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lidentOrUnderscore: FStar_Ident.ident -> FStar_Pprint.document =
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id
and maybe_paren:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p  ->
    fun e  ->
      let uu____4535 =
        let uu____4536 = unparen e in uu____4536.FStar_Parser_AST.tm in
      match uu____4535 with
      | FStar_Parser_AST.Match uu____4537 ->
          let uu____4552 = p e in soft_begin_end_with_nesting uu____4552
      | FStar_Parser_AST.TryWith uu____4553 ->
          let uu____4568 = p e in soft_begin_end_with_nesting uu____4568
      | FStar_Parser_AST.Abs
          ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,uu____4570);
             FStar_Parser_AST.prange = uu____4571;_}::[],{
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Match
                                                             (maybe_x,uu____4573);
                                                           FStar_Parser_AST.range
                                                             = uu____4574;
                                                           FStar_Parser_AST.level
                                                             = uu____4575;_})
          when matches_var maybe_x x ->
          let uu____4602 = p e in soft_begin_end_with_nesting uu____4602
      | uu____4603 -> p e
and p_term: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4605 =
      let uu____4606 = unparen e in uu____4606.FStar_Parser_AST.tm in
    match uu____4605 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4609 =
          let uu____4610 =
            let uu____4611 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4611 FStar_Pprint.semi in
          FStar_Pprint.group uu____4610 in
        let uu____4612 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4609 uu____4612
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4616 =
          let uu____4617 =
            let uu____4618 =
              let uu____4619 = str "do" in
              let uu____4620 =
                let uu____4621 =
                  let uu____4622 = p_tuplePattern x in
                  let uu____4623 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow in
                  FStar_Pprint.op_Hat_Hat uu____4622 uu____4623 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4621 in
              FStar_Pprint.op_Hat_Hat uu____4619 uu____4620 in
            let uu____4624 =
              let uu____4625 = maybe_paren p_noSeqTerm e1 in
              let uu____4626 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4625 uu____4626 in
            op_Hat_Slash_Plus_Hat uu____4618 uu____4624 in
          FStar_Pprint.group uu____4617 in
        let uu____4627 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4616 uu____4627
    | uu____4628 ->
        let uu____4629 = p_noSeqTerm e in FStar_Pprint.group uu____4629
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4632 =
      let uu____4633 = unparen e in uu____4633.FStar_Parser_AST.tm in
    match uu____4632 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4638 =
          let uu____4639 = p_tmIff e1 in
          let uu____4640 =
            let uu____4641 =
              let uu____4642 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4642 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4641 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4639 uu____4640 in
        FStar_Pprint.group uu____4638
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4648 =
          let uu____4649 = p_tmIff e1 in
          let uu____4650 =
            let uu____4651 =
              let uu____4652 =
                let uu____4653 = p_typ t in
                let uu____4654 =
                  let uu____4655 = str "by" in
                  let uu____4656 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4655 uu____4656 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4653 uu____4654 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4652 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4651 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4649 uu____4650 in
        FStar_Pprint.group uu____4648
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4657;_},e1::e2::e3::[])
        ->
        let uu____4663 =
          let uu____4664 =
            let uu____4665 =
              let uu____4666 = p_atomicTermNotQUident e1 in
              let uu____4667 =
                let uu____4668 =
                  let uu____4669 =
                    let uu____4670 = p_term e2 in
                    soft_parens_with_nesting uu____4670 in
                  let uu____4671 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4669 uu____4671 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4668 in
              FStar_Pprint.op_Hat_Hat uu____4666 uu____4667 in
            FStar_Pprint.group uu____4665 in
          let uu____4672 =
            let uu____4673 = p_noSeqTerm e3 in jump2 uu____4673 in
          FStar_Pprint.op_Hat_Hat uu____4664 uu____4672 in
        FStar_Pprint.group uu____4663
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4674;_},e1::e2::e3::[])
        ->
        let uu____4680 =
          let uu____4681 =
            let uu____4682 =
              let uu____4683 = p_atomicTermNotQUident e1 in
              let uu____4684 =
                let uu____4685 =
                  let uu____4686 =
                    let uu____4687 = p_term e2 in
                    soft_brackets_with_nesting uu____4687 in
                  let uu____4688 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4686 uu____4688 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4685 in
              FStar_Pprint.op_Hat_Hat uu____4683 uu____4684 in
            FStar_Pprint.group uu____4682 in
          let uu____4689 =
            let uu____4690 = p_noSeqTerm e3 in jump2 uu____4690 in
          FStar_Pprint.op_Hat_Hat uu____4681 uu____4689 in
        FStar_Pprint.group uu____4680
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4700 =
          let uu____4701 = str "requires" in
          let uu____4702 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4701 uu____4702 in
        FStar_Pprint.group uu____4700
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4712 =
          let uu____4713 = str "ensures" in
          let uu____4714 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4713 uu____4714 in
        FStar_Pprint.group uu____4712
    | FStar_Parser_AST.Attributes es ->
        let uu____4718 =
          let uu____4719 = str "attributes" in
          let uu____4720 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4719 uu____4720 in
        FStar_Pprint.group uu____4718
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4724 = is_unit e3 in
        if uu____4724
        then
          let uu____4725 =
            let uu____4726 =
              let uu____4727 = str "if" in
              let uu____4728 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4727 uu____4728 in
            let uu____4729 =
              let uu____4730 = str "then" in
              let uu____4731 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4730 uu____4731 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4726 uu____4729 in
          FStar_Pprint.group uu____4725
        else
          (let e2_doc =
             let uu____4734 =
               let uu____4735 = unparen e2 in uu____4735.FStar_Parser_AST.tm in
             match uu____4734 with
             | FStar_Parser_AST.If (uu____4736,uu____4737,e31) when
                 is_unit e31 ->
                 let uu____4739 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4739
             | uu____4740 -> p_noSeqTerm e2 in
           let uu____4741 =
             let uu____4742 =
               let uu____4743 = str "if" in
               let uu____4744 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4743 uu____4744 in
             let uu____4745 =
               let uu____4746 =
                 let uu____4747 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4747 e2_doc in
               let uu____4748 =
                 let uu____4749 = str "else" in
                 let uu____4750 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4749 uu____4750 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4746 uu____4748 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4742 uu____4745 in
           FStar_Pprint.group uu____4741)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4773 =
          let uu____4774 =
            let uu____4775 = str "try" in
            let uu____4776 = p_noSeqTerm e1 in prefix2 uu____4775 uu____4776 in
          let uu____4777 =
            let uu____4778 = str "with" in
            let uu____4779 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4778 uu____4779 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4774 uu____4777 in
        FStar_Pprint.group uu____4773
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4810 =
          let uu____4811 =
            let uu____4812 = str "match" in
            let uu____4813 = p_noSeqTerm e1 in
            let uu____4814 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4812 uu____4813 uu____4814 in
          let uu____4815 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4811 uu____4815 in
        FStar_Pprint.group uu____4810
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4826 =
          let uu____4827 =
            let uu____4828 = str "let open" in
            let uu____4829 = p_quident uid in
            let uu____4830 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4828 uu____4829 uu____4830 in
          let uu____4831 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4827 uu____4831 in
        FStar_Pprint.group uu____4826
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4848 = str "let" in
          let uu____4849 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4848 uu____4849 in
        let uu____4850 =
          let uu____4851 =
            let uu____4852 =
              let uu____4853 = str "and" in
              precede_break_separate_map let_doc uu____4853 p_letbinding lbs in
            let uu____4858 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4852 uu____4858 in
          FStar_Pprint.group uu____4851 in
        let uu____4859 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4850 uu____4859
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4862;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4865;
                                                         FStar_Parser_AST.level
                                                           = uu____4866;_})
        when matches_var maybe_x x ->
        let uu____4893 =
          let uu____4894 = str "function" in
          let uu____4895 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4894 uu____4895 in
        FStar_Pprint.group uu____4893
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4906 =
          let uu____4907 = p_lident id in
          let uu____4908 =
            let uu____4909 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4909 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4907 uu____4908 in
        FStar_Pprint.group uu____4906
    | uu____4910 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4913 =
      let uu____4914 = unparen e in uu____4914.FStar_Parser_AST.tm in
    match uu____4913 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4930 =
          let uu____4931 =
            let uu____4932 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4932 FStar_Pprint.space in
          let uu____4933 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4931 uu____4933 FStar_Pprint.dot in
        let uu____4934 =
          let uu____4935 = p_trigger trigger in
          let uu____4936 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4935 uu____4936 in
        prefix2 uu____4930 uu____4934
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4952 =
          let uu____4953 =
            let uu____4954 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4954 FStar_Pprint.space in
          let uu____4955 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4953 uu____4955 FStar_Pprint.dot in
        let uu____4956 =
          let uu____4957 = p_trigger trigger in
          let uu____4958 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4957 uu____4958 in
        prefix2 uu____4952 uu____4956
    | uu____4959 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4961 =
      let uu____4962 = unparen e in uu____4962.FStar_Parser_AST.tm in
    match uu____4961 with
    | FStar_Parser_AST.QForall uu____4963 -> str "forall"
    | FStar_Parser_AST.QExists uu____4976 -> str "exists"
    | uu____4989 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___108_4901  ->
    match uu___108_4901 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5002 =
          let uu____5003 =
            let uu____5004 = str "pattern" in
            let uu____5005 =
              let uu____5006 =
                let uu____5007 = p_disjunctivePats pats in jump2 uu____5007 in
              let uu____5008 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____5006 uu____5008 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5004 uu____5005 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5003 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5002
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____5014 = str "\\/" in
    FStar_Pprint.separate_map uu____5014 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____5020 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____5020
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5022 =
      let uu____5023 = unparen e in uu____5023.FStar_Parser_AST.tm in
    match uu____5022 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____5030 =
          let uu____5031 = str "fun" in
          let uu____5032 =
            let uu____5033 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____5033 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____5031 uu____5032 in
        let uu____5034 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____5030 uu____5034
    | uu____5035 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____5038  ->
    match uu____5038 with
    | (pat,when_opt,e) ->
        let uu____5054 =
          let uu____5055 =
            let uu____5056 =
              let uu____5057 =
                let uu____5058 =
                  let uu____5059 = p_disjunctivePattern pat in
                  let uu____5060 =
                    let uu____5061 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____5061 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____5059 uu____5060 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5058 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5057 in
            FStar_Pprint.group uu____5056 in
          let uu____5062 = maybe_paren p_term e in
          op_Hat_Slash_Plus_Hat uu____5055 uu____5062 in
        FStar_Pprint.group uu____5054
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___109_5047  ->
    match uu___109_5047 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5067 = str "when" in
        let uu____5068 =
          let uu____5069 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____5069 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____5067 uu____5068
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5071 =
      let uu____5072 = unparen e in uu____5072.FStar_Parser_AST.tm in
    match uu____5071 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5073;_},e1::e2::[])
        ->
        let uu____5078 = str "<==>" in
        let uu____5079 = p_tmImplies e1 in
        let uu____5080 = p_tmIff e2 in
        infix0 uu____5078 uu____5079 uu____5080
    | uu____5081 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5083 =
      let uu____5084 = unparen e in uu____5084.FStar_Parser_AST.tm in
    match uu____5083 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5085;_},e1::e2::[])
        ->
        let uu____5090 = str "==>" in
        let uu____5091 = p_tmArrow p_tmFormula e1 in
        let uu____5092 = p_tmImplies e2 in
        infix0 uu____5090 uu____5091 uu____5092
    | uu____5093 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____5098 =
        let uu____5099 = unparen e in uu____5099.FStar_Parser_AST.tm in
      match uu____5098 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5106 =
            let uu____5107 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5112 = p_binder false b in
                   let uu____5113 =
                     let uu____5114 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5114 in
                   FStar_Pprint.op_Hat_Hat uu____5112 uu____5113) bs in
            let uu____5115 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____5107 uu____5115 in
          FStar_Pprint.group uu____5106
      | uu____5116 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5118 =
      let uu____5119 = unparen e in uu____5119.FStar_Parser_AST.tm in
    match uu____5118 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5120;_},e1::e2::[])
        ->
        let uu____5125 = str "\\/" in
        let uu____5126 = p_tmFormula e1 in
        let uu____5127 = p_tmConjunction e2 in
        infix0 uu____5125 uu____5126 uu____5127
    | uu____5128 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5130 =
      let uu____5131 = unparen e in uu____5131.FStar_Parser_AST.tm in
    match uu____5130 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5132;_},e1::e2::[])
        ->
        let uu____5137 = str "/\\" in
        let uu____5138 = p_tmConjunction e1 in
        let uu____5139 = p_tmTuple e2 in
        infix0 uu____5137 uu____5138 uu____5139
    | uu____5140 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5143 =
      let uu____5144 = unparen e in uu____5144.FStar_Parser_AST.tm in
    match uu____5143 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5159 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5159
          (fun uu____5167  ->
             match uu____5167 with | (e1,uu____5173) -> p_tmEq e1) args
    | uu____5174 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5179 =
             let uu____5180 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5180 in
           FStar_Pprint.group uu____5179)
and p_tmEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ())) in
    p_tmEq' n1 e
and p_tmEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5225 =
        let uu____5226 = unparen e in uu____5226.FStar_Parser_AST.tm in
      match uu____5225 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5233 = levels op1 in
          (match uu____5233 with
           | (left1,mine,right1) ->
               let uu____5243 =
                 let uu____5244 = FStar_All.pipe_left str op1 in
                 let uu____5245 = p_tmEq' left1 e1 in
                 let uu____5246 = p_tmEq' right1 e2 in
                 infix0 uu____5244 uu____5245 uu____5246 in
               paren_if curr mine uu____5243)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5247;_},e1::e2::[])
          ->
          let uu____5252 =
            let uu____5253 = p_tmEq e1 in
            let uu____5254 =
              let uu____5255 =
                let uu____5256 =
                  let uu____5257 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5257 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5256 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5255 in
            FStar_Pprint.op_Hat_Hat uu____5253 uu____5254 in
          FStar_Pprint.group uu____5252
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5258;_},e1::[])
          ->
          let uu____5262 = levels "-" in
          (match uu____5262 with
           | (left1,mine,right1) ->
               let uu____5272 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5272)
      | uu____5273 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5328 =
        let uu____5329 = unparen e in uu____5329.FStar_Parser_AST.tm in
      match uu____5328 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5332)::(e2,uu____5334)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5354 = is_list e in Prims.op_Negation uu____5354)
          ->
          let op = "::" in
          let uu____5356 = levels op in
          (match uu____5356 with
           | (left1,mine,right1) ->
               let uu____5366 =
                 let uu____5367 = str op in
                 let uu____5368 = p_tmNoEq' left1 e1 in
                 let uu____5369 = p_tmNoEq' right1 e2 in
                 infix0 uu____5367 uu____5368 uu____5369 in
               paren_if curr mine uu____5366)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5377 = levels op in
          (match uu____5377 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5391 = p_binder false b in
                 let uu____5392 =
                   let uu____5393 =
                     let uu____5394 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5394 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5393 in
                 FStar_Pprint.op_Hat_Hat uu____5391 uu____5392 in
               let uu____5395 =
                 let uu____5396 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5397 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5396 uu____5397 in
               paren_if curr mine uu____5395)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5404 = levels op1 in
          (match uu____5404 with
           | (left1,mine,right1) ->
               let uu____5414 =
                 let uu____5415 = str op1 in
                 let uu____5416 = p_tmNoEq' left1 e1 in
                 let uu____5417 = p_tmNoEq' right1 e2 in
                 infix0 uu____5415 uu____5416 uu____5417 in
               paren_if curr mine uu____5414)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5420 =
            let uu____5421 = p_lidentOrUnderscore lid in
            let uu____5422 =
              let uu____5423 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5423 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5421 uu____5422 in
          FStar_Pprint.group uu____5420
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5444 =
            let uu____5445 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5446 =
              let uu____5447 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5447 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5445 uu____5446 in
          braces_with_nesting uu____5444
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5452;_},e1::[])
          ->
          let uu____5456 =
            let uu____5457 = str "~" in
            let uu____5458 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5457 uu____5458 in
          FStar_Pprint.group uu____5456
      | uu____5459 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5461 = p_appTerm e in
    let uu____5462 =
      let uu____5463 =
        let uu____5464 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5464 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5463 in
    FStar_Pprint.op_Hat_Hat uu____5461 uu____5462
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5469 =
            let uu____5470 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5470 t phi in
          soft_parens_with_nesting uu____5469
      | FStar_Parser_AST.TAnnotated uu____5471 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5476 ->
          let uu____5477 =
            let uu____5478 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5478 in
          failwith uu____5477
      | FStar_Parser_AST.TVariable uu____5479 ->
          let uu____5480 =
            let uu____5481 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5481 in
          failwith uu____5480
      | FStar_Parser_AST.NoName uu____5482 ->
          let uu____5483 =
            let uu____5484 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5484 in
          failwith uu____5483
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5485  ->
    match uu____5485 with
    | (lid,e) ->
        let uu____5492 =
          let uu____5493 = p_qlident lid in
          let uu____5494 =
            let uu____5495 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5495 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5493 uu____5494 in
        FStar_Pprint.group uu____5492
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5497 =
      let uu____5498 = unparen e in uu____5498.FStar_Parser_AST.tm in
    match uu____5497 with
    | FStar_Parser_AST.App uu____5499 when is_general_application e ->
        let uu____5506 = head_and_args e in
        (match uu____5506 with
         | (head1,args) ->
             let uu____5531 =
               let uu____5542 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5542
               then
                 let uu____5599 =
                   FStar_Util.take
                     (fun uu____5623  ->
                        match uu____5623 with
                        | (uu____5628,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5599 with
                 | (fs_typ_args,args1) ->
                     let uu____5666 =
                       let uu____5667 = p_indexingTerm head1 in
                       let uu____5668 =
                         let uu____5669 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5669 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5667 uu____5668 in
                     (uu____5666, args1)
               else
                 (let uu____5681 = p_indexingTerm head1 in (uu____5681, args)) in
             (match uu____5531 with
              | (head_doc,args1) ->
                  let uu____5702 =
                    let uu____5703 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5703 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5702))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5723 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5723)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5741 =
               let uu____5742 = p_quident lid in
               let uu____5743 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5742 uu____5743 in
             FStar_Pprint.group uu____5741
         | hd1::tl1 ->
             let uu____5760 =
               let uu____5761 =
                 let uu____5762 =
                   let uu____5763 = p_quident lid in
                   let uu____5764 = p_argTerm hd1 in
                   prefix2 uu____5763 uu____5764 in
                 FStar_Pprint.group uu____5762 in
               let uu____5765 =
                 let uu____5766 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5766 in
               FStar_Pprint.op_Hat_Hat uu____5761 uu____5765 in
             FStar_Pprint.group uu____5760)
    | uu____5771 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____5780 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5780 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5782 = str "#" in
        let uu____5783 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5782 uu____5783
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5785  ->
    match uu____5785 with | (e,uu____5791) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5796 =
        let uu____5797 = unparen e in uu____5797.FStar_Parser_AST.tm in
      match uu____5796 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5798;_},e1::e2::[])
          ->
          let uu____5803 =
            let uu____5804 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5805 =
              let uu____5806 =
                let uu____5807 = p_term e2 in
                soft_parens_with_nesting uu____5807 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5806 in
            FStar_Pprint.op_Hat_Hat uu____5804 uu____5805 in
          FStar_Pprint.group uu____5803
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5808;_},e1::e2::[])
          ->
          let uu____5813 =
            let uu____5814 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5815 =
              let uu____5816 =
                let uu____5817 = p_term e2 in
                soft_brackets_with_nesting uu____5817 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5816 in
            FStar_Pprint.op_Hat_Hat uu____5814 uu____5815 in
          FStar_Pprint.group uu____5813
      | uu____5818 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5821 =
      let uu____5822 = unparen e in uu____5822.FStar_Parser_AST.tm in
    match uu____5821 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5825 = p_quident lid in
        let uu____5826 =
          let uu____5827 =
            let uu____5828 = p_term e1 in soft_parens_with_nesting uu____5828 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5827 in
        FStar_Pprint.op_Hat_Hat uu____5825 uu____5826
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5834 = str (FStar_Ident.text_of_id op) in
        let uu____5835 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5834 uu____5835
    | uu____5836 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5838 =
      let uu____5839 = unparen e in uu____5839.FStar_Parser_AST.tm in
    match uu____5838 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5844 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5851 = str (FStar_Ident.text_of_id op) in
        let uu____5852 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5851 uu____5852
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5856 =
          let uu____5857 =
            let uu____5858 = str (FStar_Ident.text_of_id op) in
            let uu____5859 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5858 uu____5859 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5857 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5856
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5874 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5875 =
          let uu____5876 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5877 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5876 p_tmEq uu____5877 in
        let uu____5884 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5874 uu____5875 uu____5884
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5887 =
          let uu____5888 = p_atomicTermNotQUident e1 in
          let uu____5889 =
            let uu____5890 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5890 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5888 uu____5889 in
        FStar_Pprint.group uu____5887
    | uu____5891 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5893 =
      let uu____5894 = unparen e in uu____5894.FStar_Parser_AST.tm in
    match uu____5893 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5898 = p_quident constr_lid in
        let uu____5899 =
          let uu____5900 =
            let uu____5901 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5901 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5900 in
        FStar_Pprint.op_Hat_Hat uu____5898 uu____5899
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5903 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5903 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5905 = p_term e1 in soft_parens_with_nesting uu____5905
    | uu____5906 when is_array e ->
        let es = extract_from_list e in
        let uu____5910 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5911 =
          let uu____5912 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5912 p_noSeqTerm es in
        let uu____5913 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5910 uu____5911 uu____5913
    | uu____5914 when is_list e ->
        let uu____5915 =
          let uu____5916 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5917 = extract_from_list e in
          separate_map_or_flow uu____5916 p_noSeqTerm uu____5917 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5915 FStar_Pprint.rbracket
    | uu____5920 when is_lex_list e ->
        let uu____5921 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5922 =
          let uu____5923 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5924 = extract_from_list e in
          separate_map_or_flow uu____5923 p_noSeqTerm uu____5924 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5921 uu____5922 FStar_Pprint.rbracket
    | uu____5927 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5931 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5932 =
          let uu____5933 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5933 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5931 uu____5932 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5937 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5938 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5937 uu____5938
    | FStar_Parser_AST.Op (op,args) when
        let uu____5945 = handleable_op op args in
        Prims.op_Negation uu____5945 ->
        let uu____5946 =
          let uu____5947 =
            let uu____5948 =
              let uu____5949 =
                let uu____5950 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5950
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5949 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5948 in
          Prims.strcat "Operation " uu____5947 in
        failwith uu____5946
    | FStar_Parser_AST.Uvar uu____5951 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5952 = p_term e in soft_parens_with_nesting uu____5952
    | FStar_Parser_AST.Const uu____5953 ->
        let uu____5954 = p_term e in soft_parens_with_nesting uu____5954
    | FStar_Parser_AST.Op uu____5955 ->
        let uu____5962 = p_term e in soft_parens_with_nesting uu____5962
    | FStar_Parser_AST.Tvar uu____5963 ->
        let uu____5964 = p_term e in soft_parens_with_nesting uu____5964
    | FStar_Parser_AST.Var uu____5965 ->
        let uu____5966 = p_term e in soft_parens_with_nesting uu____5966
    | FStar_Parser_AST.Name uu____5967 ->
        let uu____5968 = p_term e in soft_parens_with_nesting uu____5968
    | FStar_Parser_AST.Construct uu____5969 ->
        let uu____5980 = p_term e in soft_parens_with_nesting uu____5980
    | FStar_Parser_AST.Abs uu____5981 ->
        let uu____5988 = p_term e in soft_parens_with_nesting uu____5988
    | FStar_Parser_AST.App uu____5989 ->
        let uu____5996 = p_term e in soft_parens_with_nesting uu____5996
    | FStar_Parser_AST.Let uu____5997 ->
        let uu____6010 = p_term e in soft_parens_with_nesting uu____6010
    | FStar_Parser_AST.LetOpen uu____6011 ->
        let uu____6016 = p_term e in soft_parens_with_nesting uu____6016
    | FStar_Parser_AST.Seq uu____6017 ->
        let uu____6022 = p_term e in soft_parens_with_nesting uu____6022
    | FStar_Parser_AST.Bind uu____6023 ->
        let uu____6030 = p_term e in soft_parens_with_nesting uu____6030
    | FStar_Parser_AST.If uu____6031 ->
        let uu____6038 = p_term e in soft_parens_with_nesting uu____6038
    | FStar_Parser_AST.Match uu____6039 ->
        let uu____6054 = p_term e in soft_parens_with_nesting uu____6054
    | FStar_Parser_AST.TryWith uu____6055 ->
        let uu____6070 = p_term e in soft_parens_with_nesting uu____6070
    | FStar_Parser_AST.Ascribed uu____6071 ->
        let uu____6080 = p_term e in soft_parens_with_nesting uu____6080
    | FStar_Parser_AST.Record uu____6081 ->
        let uu____6094 = p_term e in soft_parens_with_nesting uu____6094
    | FStar_Parser_AST.Project uu____6095 ->
        let uu____6100 = p_term e in soft_parens_with_nesting uu____6100
    | FStar_Parser_AST.Product uu____6101 ->
        let uu____6108 = p_term e in soft_parens_with_nesting uu____6108
    | FStar_Parser_AST.Sum uu____6109 ->
        let uu____6116 = p_term e in soft_parens_with_nesting uu____6116
    | FStar_Parser_AST.QForall uu____6117 ->
        let uu____6130 = p_term e in soft_parens_with_nesting uu____6130
    | FStar_Parser_AST.QExists uu____6131 ->
        let uu____6144 = p_term e in soft_parens_with_nesting uu____6144
    | FStar_Parser_AST.Refine uu____6145 ->
        let uu____6150 = p_term e in soft_parens_with_nesting uu____6150
    | FStar_Parser_AST.NamedTyp uu____6151 ->
        let uu____6156 = p_term e in soft_parens_with_nesting uu____6156
    | FStar_Parser_AST.Requires uu____6157 ->
        let uu____6164 = p_term e in soft_parens_with_nesting uu____6164
    | FStar_Parser_AST.Ensures uu____6165 ->
        let uu____6172 = p_term e in soft_parens_with_nesting uu____6172
    | FStar_Parser_AST.Assign uu____6173 ->
        let uu____6178 = p_term e in soft_parens_with_nesting uu____6178
    | FStar_Parser_AST.Attributes uu____6179 ->
        let uu____6182 = p_term e in soft_parens_with_nesting uu____6182
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___112_6167  ->
    match uu___112_6167 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6187 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6187
    | FStar_Const.Const_string (s,uu____6189) ->
        let uu____6190 = str s in FStar_Pprint.dquotes uu____6190
    | FStar_Const.Const_bytearray (bytes,uu____6192) ->
        let uu____6197 =
          let uu____6198 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6198 in
        let uu____6199 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6197 uu____6199
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___110_6201 =
          match uu___110_6201 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___111_6205 =
          match uu___111_6205 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6232  ->
               match uu____6232 with
               | (s,w) ->
                   let uu____6239 = signedness s in
                   let uu____6240 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6239 uu____6240)
            sign_width_opt in
        let uu____6241 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6241 ending
    | FStar_Const.Const_range r ->
        let uu____6243 = FStar_Range.string_of_range r in str uu____6243
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6245 = p_quident lid in
        let uu____6246 =
          let uu____6247 =
            let uu____6248 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6248 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6247 in
        FStar_Pprint.op_Hat_Hat uu____6245 uu____6246
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6250 = str "u#" in
    let uu____6251 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6250 uu____6251
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6253 =
      let uu____6254 = unparen u in uu____6254.FStar_Parser_AST.tm in
    match uu____6253 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6255;_},u1::u2::[])
        ->
        let uu____6260 =
          let uu____6261 = p_universeFrom u1 in
          let uu____6262 =
            let uu____6263 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6263 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6261 uu____6262 in
        FStar_Pprint.group uu____6260
    | FStar_Parser_AST.App uu____6264 ->
        let uu____6271 = head_and_args u in
        (match uu____6271 with
         | (head1,args) ->
             let uu____6296 =
               let uu____6297 = unparen head1 in
               uu____6297.FStar_Parser_AST.tm in
             (match uu____6296 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6299 =
                    let uu____6300 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6301 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6309  ->
                           match uu____6309 with
                           | (u1,uu____6315) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6300 uu____6301 in
                  FStar_Pprint.group uu____6299
              | uu____6316 ->
                  let uu____6317 =
                    let uu____6318 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6318 in
                  failwith uu____6317))
    | uu____6319 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6321 =
      let uu____6322 = unparen u in uu____6322.FStar_Parser_AST.tm in
    match uu____6321 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6345 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6345
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6346;_},uu____6347::uu____6348::[])
        ->
        let uu____6351 = p_universeFrom u in
        soft_parens_with_nesting uu____6351
    | FStar_Parser_AST.App uu____6352 ->
        let uu____6359 = p_universeFrom u in
        soft_parens_with_nesting uu____6359
    | uu____6360 ->
        let uu____6361 =
          let uu____6362 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6362 in
        failwith uu____6361
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let signature_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_justSig e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let pat_to_document: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p
let binder_to_document: FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____6435,decls) ->
           let uu____6441 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6441
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6450,decls,uu____6452) ->
           let uu____6457 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6457
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6536  ->
         match uu____6536 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____6578,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6584,decls,uu____6586) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6658 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6671;
                 FStar_Parser_AST.doc = uu____6672;
                 FStar_Parser_AST.quals = uu____6673;
                 FStar_Parser_AST.attrs = uu____6674;_}::uu____6675 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6681 =
                   let uu____6684 =
                     let uu____6687 = FStar_List.tl ds in d :: uu____6687 in
                   d0 :: uu____6684 in
                 (uu____6681, (d0.FStar_Parser_AST.drange))
             | uu____6692 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6658 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6777 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6777 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6954 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6954, comments1))))))
