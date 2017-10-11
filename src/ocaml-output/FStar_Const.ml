open Prims
type signedness = FStar_Util.signedness[@@deriving show]
type width = FStar_Util.width[@@deriving show]
type sconst =
  | Const_effect
  | Const_unit
  | Const_bool of Prims.bool
  | Const_int of
  (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Const_char of FStar_BaseTypes.char
  | Const_float of FStar_BaseTypes.double
  | Const_bytearray of (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Const_string of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Const_range of FStar_Range.range
  | Const_reify
  | Const_reflect of FStar_Ident.lid[@@deriving show]
let uu___is_Const_effect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____57 -> false
let uu___is_Const_unit: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____62 -> false
let uu___is_Const_bool: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____68 -> false
let __proj__Const_bool__item___0: sconst -> Prims.bool =
  fun projectee  -> match projectee with | Const_bool _0 -> _0
let uu___is_Const_int: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____92 -> false
let __proj__Const_int__item___0:
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_int _0 -> _0
let uu___is_Const_char: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____136 -> false
let __proj__Const_char__item___0: sconst -> FStar_BaseTypes.char =
  fun projectee  -> match projectee with | Const_char _0 -> _0
let uu___is_Const_float: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____150 -> false
let __proj__Const_float__item___0: sconst -> FStar_BaseTypes.double =
  fun projectee  -> match projectee with | Const_float _0 -> _0
let uu___is_Const_bytearray: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____170 -> false
let __proj__Const_bytearray__item___0:
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0
let uu___is_Const_string: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____206 -> false
let __proj__Const_string__item___0:
  sconst -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Const_string _0 -> _0
let uu___is_Const_range: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____232 -> false
let __proj__Const_range__item___0: sconst -> FStar_Range.range =
  fun projectee  -> match projectee with | Const_range _0 -> _0
let uu___is_Const_reify: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____245 -> false
let uu___is_Const_reflect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____251 -> false
let __proj__Const_reflect__item___0: sconst -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0
let eq_const: sconst -> sconst -> Prims.bool =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____300 = FStar_Util.ensure_decimal s1 in
           let uu____301 = FStar_Util.ensure_decimal s2 in
           uu____300 = uu____301) && (o1 = o2)
      | (Const_bytearray (a,uu____309),Const_bytearray (b,uu____311)) ->
          a = b
      | (Const_string (a,uu____323),Const_string (b,uu____325)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____328 -> c1 = c2
let rec pow2: Prims.int -> Prims.int =
  fun x  ->
    match x with
    | _0_27 when _0_27 = (Prims.parse_int "0") -> Prims.parse_int "1"
    | uu____337 ->
        let uu____338 = pow2 (x - (Prims.parse_int "1")) in
        (Prims.parse_int "2") * uu____338
let bounds:
  FStar_Util.signedness ->
    FStar_Util.width -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun signedness  ->
    fun width  ->
      let n1 =
        match width with
        | FStar_Util.Int8  -> Prims.parse_int "8"
        | FStar_Util.Int16  -> Prims.parse_int "16"
        | FStar_Util.Int32  -> Prims.parse_int "32"
        | FStar_Util.Int64  -> Prims.parse_int "64" in
      let uu____352 =
        match signedness with
        | FStar_Util.Unsigned  ->
            let uu____361 =
              let uu____362 = pow2 n1 in uu____362 - (Prims.parse_int "1") in
            ((Prims.parse_int "0"), uu____361)
        | FStar_Util.Signed  ->
            let upper = pow2 (n1 - (Prims.parse_int "1")) in
            ((- upper), (upper - (Prims.parse_int "1"))) in
      match uu____352 with | (lower,upper) -> (lower, upper)