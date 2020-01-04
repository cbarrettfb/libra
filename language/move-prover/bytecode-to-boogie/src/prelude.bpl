// ================================================================================
// Domains


// Path type
// ---------

type Edge = int; // both FieldName and vector index are mapped to int

type {:datatype} Path;
function {:constructor} Path(p: [int]Edge, size: int): Path;
const EmptyPath: Path;
axiom size#Path(EmptyPath) == 0;

function {:inline} path_index_at(p: Path, i: int): int {
    p#Path(p)[i]
}

// Type Values
// -----------

type TypeName;
type FieldName = int;
type LocalName;
type {:datatype} TypeValue;
function {:constructor} BooleanType() : TypeValue;
function {:constructor} IntegerType() : TypeValue;
function {:constructor} AddressType() : TypeValue;
function {:constructor} ByteArrayType() : TypeValue;
function {:constructor} StrType() : TypeValue;
function {:constructor} VectorType(t: TypeValue) : TypeValue;
function {:constructor} StructType(name: TypeName, ts: TypeValueArray) : TypeValue;
const DefaultTypeValue: TypeValue;
function {:builtin "MapConst"} MapConstTypeValue(tv: TypeValue): [int]TypeValue;

type {:datatype} TypeValueArray;
function {:constructor} TypeValueArray(v: [int]TypeValue, l: int): TypeValueArray;
const EmptyTypeValueArray: TypeValueArray;
axiom l#TypeValueArray(EmptyTypeValueArray) == 0;
axiom v#TypeValueArray(EmptyTypeValueArray) == MapConstTypeValue(DefaultTypeValue);

function {:inline} ExtendTypeValueArray(ta: TypeValueArray, tv: TypeValue): TypeValueArray {
    TypeValueArray(v#TypeValueArray(ta)[l#TypeValueArray(ta) := tv], l#TypeValueArray(ta) + 1)
}


// Values
// ------

type Address = int;
type ByteArray;
type String;
type {:datatype} Value;

const MAX_U64: int;
axiom MAX_U64 == 9223372036854775807;

function {:constructor} Boolean(b: bool): Value;
function {:constructor} Integer(i: int): Value;
function {:constructor} Address(a: Address): Value;
function {:constructor} ByteArray(b: ByteArray): Value;
function {:constructor} Str(a: String): Value;
function {:constructor} Vector(v: ValueArray): Value; // used to both represent move Struct and Vector

// ValueSeq
// -----------

type {:builtindecl ""} {:builtin "(Seq T@Value)"} ValueSeq;
function {:builtin "(as seq.empty (Seq T@Value))"} EmptyValueSeq(): ValueSeq;
function {:builtin "seq.len"} ValueSeqLen(a: ValueSeq): int;
function {:builtin "seq.++"} ValueSeqConcat(a: ValueSeq, b:ValueSeq): ValueSeq;
function {:builtin "seq.++"} ValueSeqConcat3(a: ValueSeq, b:ValueSeq, c:ValueSeq): ValueSeq;
function {:builtin "seq.unit"} ValueSeqUnit(v: Value): ValueSeq;
function {:builtin "seq.nth"} ValueSeqNth(a: ValueSeq, i: int): Value;
function {:builtin "seq.extract"} ValueSeqExtract(a: ValueSeq, i: int, j: int): ValueSeq;

const DefaultValue: Value;


// Value Array
// -----------

type {:datatype} {:dependson "Value"} ValueArray;

function {:constructor} ValueArray(v: ValueSeq): ValueArray;

function {:inline} EmptyValueArray(): ValueArray {
    ValueArray(EmptyValueSeq())
}
function {:inline} AddValueArray(a: ValueArray, v: Value): ValueArray {
    ValueArray(ValueSeqConcat(v#ValueArray(a),ValueSeqUnit(v)))
}
function {:inline} RemoveValueArray(a: ValueArray): ValueArray {
    ValueArray(ValueSeqExtract(v#ValueArray(a), 0, ValueSeqLen(v#ValueArray(a)) - 1))
}
function {:inline} ConcatValueArray(a1: ValueArray, a2: ValueArray): ValueArray {
    ValueArray(ValueSeqConcat(v#ValueArray(a1), v#ValueArray(a2)))
}
// TODO: fix these
procedure {:inline 1} ReverseValueArray(a: ValueArray) returns (ret: ValueArray)
{
    var len : int;
    len := ValueSeqLen(v#ValueArray(a));
    assume ValueSeqLen(v#ValueArray(ret)) == len;
    assume (forall i: int :: 0 <= i && i < len ==> ValueSeqNth(v#ValueArray(ret), i) == ValueSeqNth(v#ValueArray(a), len - i - 1));
}
function {:inline} UpdateValueArray(a: ValueArray, i: int, elem: Value): ValueArray {
    if (i == 0) then
      if (ValueSeqLen(v#ValueArray(a)) == 1) then
        ValueArray(ValueSeqUnit(elem))
      else
        ValueArray(ValueSeqConcat(ValueSeqUnit(elem), ValueSeqExtract(v#ValueArray(a), 1, ValueSeqLen(v#ValueArray(a)) - 1)))
    else if (i == ValueSeqLen(v#ValueArray(a)) - 1) then
        ValueArray(ValueSeqConcat(ValueSeqExtract(v#ValueArray(a), 0, ValueSeqLen(v#ValueArray(a)) - 1), ValueSeqUnit(elem)))
    else
        ValueArray(ValueSeqConcat3(ValueSeqExtract(v#ValueArray(a), 0, i), ValueSeqUnit(elem),
	                           ValueSeqExtract(v#ValueArray(a), i + 1, ValueSeqLen(v#ValueArray(a)) - i - 1)))
}
function {:inline} SwapValueArray(a: ValueArray, i: int, j: int): ValueArray {
    a
}
function {:inline} IsEmpty(a: ValueArray): bool {
    ValueSeqLen(v#ValueArray(a)) == 0
}


// Stratified Functions on Values
// ------------------------------

// TODO: templatize this or move it back to the translator. For now we
//   prefer to handcode this so its easier to evolve the model independent of the
//   translator.

// STRATIFICATION_DEPTH: 4

// function {:inline} IsEqual4(v1: Value, v2: Value): bool {
//     v1 == v2
// }
// function {:inline} IsEqual3(v1: Value, v2: Value): bool {
//     (v1 == v2) ||
//     (is#Vector(v1) &&
//      is#Vector(v2) &&
//      vlen(v1) == vlen(v2) &&
//      (forall i: int :: 0 <= i && i < vlen(v1) ==> IsEqual4(vmap(v1, i), vmap(v2, i))))
// }
// function {:inline} IsEqual2(v1: Value, v2: Value): bool {
//     (v1 == v2) ||
//     (is#Vector(v1) &&
//      is#Vector(v2) &&
//      vlen(v1) == vlen(v2) &&
//      (forall i: int :: 0 <= i && i < vlen(v1) ==> IsEqual3(vmap(v1,i), vmap(v2,i))))
// }
// function {:inline} IsEqual1(v1: Value, v2: Value): bool {
//     (v1 == v2) ||
//     (is#Vector(v1) &&
//      is#Vector(v2) &&
//      vlen(v1) == vlen(v2) &&
//      (forall i: int :: 0 <= i && i < vlen(v1) ==> IsEqual2(vmap(v1,i), vmap(v2,i))))
// }
function {:inline} IsEqual(v1: Value, v2: Value): bool {
    v1 == v2
}

function {:inline} ReadValue2(p: Path, v: Value) : Value {
    v
}
function {:inline} ReadValue1(p: Path, v: Value) : Value {
    if (1 == size#Path(p)) then
        v
    else
        ReadValue2(p, vmap(v,path_index_at(p, 1)))
}
function {:inline} ReadValue0(p: Path, v: Value) : Value {
    if (0 == size#Path(p)) then
        v
    else
        ReadValue1(p, vmap(v,path_index_at(p, 0)))
}
function {:inline} ReadValue(p: Path, v: Value): Value {
    ReadValue0(p, v)
}

function {:inline} UpdateValue2(p: Path, v: Value, new_v: Value): Value {
    new_v
}
function {:inline} UpdateValue1(p: Path, v: Value, new_v: Value): Value {
    if (1 == size#Path(p)) then
        new_v
    else
        update_vector(v, path_index_at(p, 1), UpdateValue2(p, vmap(v,path_index_at(p, 1)), new_v))
}
function {:inline} UpdateValue0(p: Path, v: Value, new_v: Value): Value {
    if (0 == size#Path(p)) then
        new_v
    else
        update_vector(v, path_index_at(p, 0), UpdateValue1(p, vmap(v,path_index_at(p, 0)), new_v))
}
function {:inline} UpdateValue(p: Path, v: Value, new_v: Value): Value {
    UpdateValue0(p, v, new_v)
}

// Vector related functions on values
// ----------------------------------

function {:inline} vmap(v: Value, i: int): Value {
    ValueSeqNth(v#ValueArray(v#Vector(v)), i)
}
function {:inline} vlen(v: Value): int {
    ValueSeqLen(v#ValueArray(v#Vector(v)))
}
function {:inline} mk_vector(): Value {
    Vector(EmptyValueArray())
}
function {:inline} push_back_vector(v: Value, elem: Value): Value {
    Vector(AddValueArray(v#Vector(v), elem))
}
function {:inline} pop_back_vector(v: Value): Value {
    Vector(RemoveValueArray(v#Vector(v)))
}
function {:inline} append_vector(v1: Value, v2: Value): Value {
    Vector(ConcatValueArray(v#Vector(v1), v#Vector(v2)))
}
procedure {:inline 1} reverse_vector(v: Value) returns (ret: Value) {
    var r: ValueArray;
    call r := ReverseValueArray(v#Vector(v));
    ret := Vector(r);
}
function {:inline} update_vector(v: Value, i: int, elem: Value): Value {
    Vector(UpdateValueArray(v#Vector(v), i, elem))
}
function {:inline} swap_vector(v: Value, i: int, j: int): Value {
    Vector(SwapValueArray(v#Vector(v), i, j))
}

// ============================================================================================
// Memory

type {:datatype} Location;
function {:constructor} Global(t: TypeValue, a: Address): Location;
function {:constructor} Local(i: int): Location;

type {:datatype} Reference;
function {:constructor} Reference(l: Location, p: Path): Reference;
const DefaultReference: Reference;

type {:datatype} Memory;
function {:constructor} Memory(domain: [Location]bool, contents: [Location]Value): Memory;

function {:builtin "MapConst"} ConstMemoryDomain(v: bool): [Location]bool;
function {:builtin "MapConst"} ConstMemoryContent(v: Value): [Location]Value;

const EmptyMemory: Memory;
axiom domain#Memory(EmptyMemory) == ConstMemoryDomain(false);
axiom contents#Memory(EmptyMemory) == ConstMemoryContent(DefaultValue);

var m : Memory;
var local_counter : int;
var abort_flag: bool;

function {:inline} GetLocal(m: Memory, idx: int): Value {
   contents#Memory(m)[Local(idx)]
}

function {:inline} UpdateLocal(m: Memory, idx: int, v: Value): Memory {
    Memory(domain#Memory(m)[Local(idx) := true], contents#Memory(m)[Local(idx) := v])
}

procedure {:inline 1} InitMemory() {
  m := EmptyMemory;
  local_counter := 0;
}

// ============================================================================================
// Specifications

// TODO: unify some of this with instruction procedures to avoid duplication

// Tests whether resource exists.
function {:inline} ExistsResourceRaw(m: Memory, resource: TypeValue, addr: Address): bool {
    domain#Memory(m)[Global(resource, addr)]
}
function {:inline} ExistsResource(m: Memory, resource: TypeValue, addr: Address): Value {
    Boolean(ExistsResourceRaw(m, resource, addr))
}

// Obtains reference to the given resource.
function {:inline} GetResourceReference(resource: TypeValue, addr: Address): Reference {
    Reference(Global(resource, addr), EmptyPath)
}

// Obtains reference to local.
function {:inline} GetLocalReference(frame_idx: int, idx: int): Reference {
    Reference(Local(frame_idx + idx), EmptyPath)
}

// Applies a field selection to the reference.
function {:inline} SelectFieldFromRef(ref: Reference, field: FieldName): Reference {
    Reference(
      l#Reference(ref),
      Path(p#Path(p#Reference(ref))[size#Path(p#Reference(ref)) := field], size#Path(p#Reference(ref)) + 1)
    )
}

// Applies a field selection to a value.
function {:inline} SelectField(val: Value, field: FieldName): Value {
    vmap(val,field)
}

// Dereferences a reference.
function {:inline} Dereference(m: Memory, ref: Reference): Value {
    ReadValue(p#Reference(ref), contents#Memory(m)[l#Reference(ref)])
}

// Checker whether sender account exists.
function {:inline} ExistsTxnSenderAccount(m: Memory, txn: Transaction): bool {
   // TODO: need to verify whether this is the intended semantics. We assume right now
   //   we can identify sender account existence if there is any resource under the sender address.
   // (exists resource: TypeValue :: domain#Memory(m)[Global(resource, sender#Transaction(txn))])
   true
}

// Returns sender address.
function {:inline} TxnSenderAddress(txn: Transaction): Address {
  sender#Transaction(txn)
}


// ============================================================================================
// Instructions

procedure {:inline 1} Exists(address: Value, t: TypeValue) returns (dst: Value)
{
    assume is#Address(address);
    dst := ExistsResource(m, t, a#Address(address));
}

procedure {:inline 1} MoveToSender(ta: TypeValue, v: Value)
{
    var a: Address;
    var l: Location;

    a := sender#Transaction(txn);
    l := Global(ta, a);
    if (ExistsResourceRaw(m, ta, a)) {
        abort_flag := true;
        return;
    }
    m := Memory(domain#Memory(m)[l := true], contents#Memory(m)[l := v]);
}

procedure {:inline 1} MoveFrom(address: Value, ta: TypeValue) returns (dst: Value)
{
    var a: Address;
    var l: Location;
    assume is#Address(address);
    a := a#Address(address);
    l := Global(ta, a);
    if (!ExistsResourceRaw(m, ta, a)) {
        abort_flag := true;
        return;
    }
    dst := contents#Memory(m)[l];
    m := Memory(domain#Memory(m)[l := false], contents#Memory(m)[l := DefaultValue]);
}

procedure {:inline 1} BorrowGlobal(address: Value, ta: TypeValue) returns (dst: Reference)
{
    var a: Address;
    var v: Value;
    var l: Location;
    assume is#Address(address);
    a := a#Address(address);
    l := Global(ta, a);
    if (!ExistsResourceRaw(m, ta, a)) {
        abort_flag := true;
        return;
    }
    dst := Reference(l, EmptyPath);
}

procedure {:inline 1} BorrowLoc(l: int) returns (dst: Reference)
{
    dst := Reference(Local(l), EmptyPath);
}

procedure {:inline 1} BorrowField(src: Reference, f: FieldName) returns (dst: Reference)
{
    var p: Path;
    var size: int;

    p := p#Reference(src);
    size := size#Path(p);
	p := Path(p#Path(p)[size := f], size+1);
    dst := Reference(l#Reference(src), p);
}

procedure {:inline 1} WriteRef(to: Reference, new_v: Value)
{
    var l: Location;
    var v: Value;

    l := l#Reference(to);
    v := contents#Memory(m)[l];
    v := UpdateValue(p#Reference(to), v, new_v);
    m := Memory(domain#Memory(m), contents#Memory(m)[l := v]);
}

procedure {:inline 1} ReadRef(from: Reference) returns (v: Value)
{
    v := ReadValue(p#Reference(from), contents#Memory(m)[l#Reference(from)]);
}

procedure {:inline 1} CopyOrMoveRef(local: Reference) returns (dst: Reference)
{
    dst := local;
}

procedure {:inline 1} CopyOrMoveValue(local: Value) returns (dst: Value)
{
    dst := local;
}

procedure {:inline 1} FreezeRef(src: Reference) returns (dst: Reference)
{
    dst := src;
}

// Pack and Unpack are auto-generated for each type T

procedure {:inline 1} Add(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    if (i#Integer(src1) + i#Integer(src2) > MAX_U64) {
        abort_flag := true;
        return;
    }
    dst := Integer(i#Integer(src1) + i#Integer(src2));
}

procedure {:inline 1} Sub(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    if (i#Integer(src1) < i#Integer(src2)) {
        abort_flag := true;
        return;
    }
    dst := Integer(i#Integer(src1) - i#Integer(src2));
}

procedure {:inline 1} Mul(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    if (i#Integer(src1) * i#Integer(src2) > MAX_U64) {
        abort_flag := true;
        return;
    }
    dst := Integer(i#Integer(src1) * i#Integer(src2));
}

procedure {:inline 1} Div(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    if (i#Integer(src2) == 0) {
        abort_flag := true;
        return;
    }
    dst := Integer(i#Integer(src1) div i#Integer(src2));
}

procedure {:inline 1} Mod(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    if (i#Integer(src2) == 0) {
        abort_flag := true;
        return;
    }
    dst := Integer(i#Integer(src1) mod i#Integer(src2));
}

procedure {:inline 1} Lt(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    dst := Boolean(i#Integer(src1) < i#Integer(src2));
}

procedure {:inline 1} Gt(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    dst := Boolean(i#Integer(src1) > i#Integer(src2));
}

procedure {:inline 1} Le(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    dst := Boolean(i#Integer(src1) <= i#Integer(src2));
}

procedure {:inline 1} Ge(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Integer(src1) && is#Integer(src2);
    dst := Boolean(i#Integer(src1) >= i#Integer(src2));
}

procedure {:inline 1} And(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Boolean(src1) && is#Boolean(src2);
    dst := Boolean(b#Boolean(src1) && b#Boolean(src2));
}

procedure {:inline 1} Or(src1: Value, src2: Value) returns (dst: Value)
{
    assume is#Boolean(src1) && is#Boolean(src2);
    dst := Boolean(b#Boolean(src1) || b#Boolean(src2));
}

procedure {:inline 1} Not(src: Value) returns (dst: Value)
{
    assume is#Boolean(src);
    dst := Boolean(!b#Boolean(src));
}

procedure {:inline 1} LdConst(val: int) returns (ret: Value)
{
    ret := Integer(val);
}

procedure {:inline 1} LdAddr(val: Address) returns (ret: Value)
{
    ret := Address(val);
}

procedure {:inline 1} LdByteArray(val: ByteArray) returns (ret: Value)
{
    ret := ByteArray(val);
}

procedure {:inline 1} LdStr(val: String) returns (ret: Value)
{
    ret := Str(val);
}

procedure {:inline 1} LdTrue() returns (ret: Value)
{
    ret := Boolean(true);
}

procedure {:inline 1} LdFalse() returns (ret: Value)
{
    ret := Boolean(false);
}

// Transaction builtin instructions
// --------------------------------

type {:datatype} Transaction;
var txn: Transaction;
function {:constructor} Transaction(
  gas_unit_price: int, max_gas_units: int, public_key: ByteArray,
  sender: Address, sequence_number: int, gas_remaining: int) : Transaction;

const some_key: ByteArray;

procedure {:inline 1} InitTransaction(sender: Address) {
  txn := Transaction(1, 1000, some_key, sender, 0, 1000);
}

procedure {:inline 1} GetGasRemaining() returns (ret_gas_remaining: Value)
{
  ret_gas_remaining := Integer(gas_remaining#Transaction(txn));
}

procedure {:inline 1} GetTxnSequenceNumber() returns (ret_sequence_number: Value)
{
  ret_sequence_number := Integer(sequence_number#Transaction(txn));
}

procedure {:inline 1} GetTxnPublicKey() returns (ret_public_key: Value)
{
  ret_public_key := ByteArray(public_key#Transaction(txn));
}

procedure {:inline 1} GetTxnSenderAddress() returns (ret_sender: Value)
{
  ret_sender := Address(sender#Transaction(txn));
}

procedure {:inline 1} GetTxnMaxGasUnits() returns (ret_max_gas_units: Value)
{
  ret_max_gas_units := Integer(max_gas_units#Transaction(txn));
}

procedure {:inline 1} GetTxnGasUnitPrice() returns (ret_gas_unit_price: Value)
{
  ret_gas_unit_price := Integer(gas_unit_price#Transaction(txn));
}

// ==================================================================================
// Native Vector Type

function {:inline} Vector_T_type_value(tv: TypeValue): TypeValue {
    VectorType(tv)
}

procedure {:inline 1} Vector_empty(ta: TypeValue) returns (v: Value) {
    v := mk_vector();
}

procedure {:inline 1} Vector_is_empty(ta: TypeValue, r: Reference) returns (b: Value) {
    var v: Value;
    v := Dereference(m, r);
    assume is#Vector(v);
    b := Boolean(vlen(v) == 0);
}

procedure {:inline 1} Vector_push_back(ta: TypeValue, r: Reference, val: Value) {
    var v: Value;
    v := Dereference(m, r);
    assume is#Vector(v);
    call WriteRef(r, push_back_vector(v, val));
}

procedure {:inline 1} Vector_pop_back(ta: TypeValue, r: Reference) returns (e: Value){
    var v: Value;
    var len: int;
    v := Dereference(m, r);
    assume is#Vector(v);
    len := vlen(v);
    if (len == 0) {
        abort_flag := true;
        return;
    }
    e := vmap(v,len-1);
    call WriteRef(r, pop_back_vector(v));
}

procedure {:inline 1} Vector_append(ta: TypeValue, r: Reference, other: Value) {
    var v: Value;
    v := Dereference(m, r);
    assume is#Vector(v);
    assume is#Vector(other);
    call WriteRef(r, append_vector(v, other));
}

procedure {:inline 1} Vector_reverse(ta: TypeValue, r: Reference) {
    var v: Value;
    v := Dereference(m, r);
    assume is#Vector(v);
    call v := reverse_vector(v);
    call WriteRef(r, v);
}

procedure {:inline 1} Vector_length(ta: TypeValue, r: Reference) returns (l: Value) {
    var v: Value;
    v := Dereference(m, r);
    assume is#Vector(v);
    l := Integer(vlen(v));
}

procedure {:inline 1} Vector_borrow(ta: TypeValue, src: Reference, index: Value) returns (dst: Reference) {
    call dst := Vector_borrow_mut(ta, src, index);
}

procedure {:inline 1} Vector_borrow_mut(ta: TypeValue, src: Reference, index: Value) returns (dst: Reference) {
    var p: Path;
    var size: int;
    var i_ind: int;
    var v: Value;

    assume is#Integer(index);
    i_ind := i#Integer(index);
    v := Dereference(m, src);
    assume is#Vector(v);
    if (i_ind < 0 || i_ind >= vlen(v)) {
        abort_flag := true;
        return;
    }

    p := p#Reference(src);
    size := size#Path(p);
	p := Path(p#Path(p)[size := i_ind], size+1);
    dst := Reference(l#Reference(src), p);
}

procedure {:inline 1} Vector_destroy_empty(ta: TypeValue, v: Value) {
    if (vlen(v) != 0) {
      abort_flag := true;
    }
}

procedure {:inline 1} Vector_swap(ta: TypeValue, src: Reference, i: Value, j: Value)
{
    var i_ind: int;
    var j_ind: int;
    var v: Value;
    assume is#Integer(i);
    assume is#Integer(j);
    i_ind := i#Integer(i);
    j_ind := i#Integer(j);
    v := Dereference(m, src);
    if (i_ind >= vlen(v) || j_ind >= vlen(v) || i_ind < 0 || j_ind < 0) {
        abort_flag := true;
        return;
    }
    v := swap_vector(v, i_ind, j_ind);
    call WriteRef(src, v);
}

procedure {:inline 1} Vector_get(ta: TypeValue, src: Reference, i: Value) returns (e: Value)
requires vlen(Dereference(m, src)) > i#Integer(i);
{
    var i_ind: int;
    var v: Value;

    assume is#Integer(i);
    i_ind := i#Integer(i);
    v := Dereference(m, src);
    assume is#Vector(v);
    if (i_ind < 0 || i_ind >= vlen(v)) {
        abort_flag := true;
        return;
    }
    e := vmap(v,i_ind);
}

procedure {:inline 1} Vector_set(ta: TypeValue, src: Reference, i: Value, e: Value) {
    var i_ind: int;
    var v: Value;

    assume is#Integer(i);
    i_ind := i#Integer(i);
    v := Dereference(m, src);
    assume is#Vector(v);
    if (i_ind < 0 || i_ind >= vlen(v)) {
        abort_flag := true;
        return;
    }
    v := update_vector(v, i_ind, e);
    call WriteRef(src, v);
}
