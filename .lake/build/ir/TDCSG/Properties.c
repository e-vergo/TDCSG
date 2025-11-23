// Lean compiler output
// Module: TDCSG.Properties
// Imports: Init TDCSG.Basic Mathlib.Topology.MetricSpace.Isometry Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_PiecewiseIsometry_id___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_id(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___redArg(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_PiecewiseIsometry_id___closed__0;
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_inc(x_10);
return x_10;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PiecewiseIsometry_mk__of__set___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__of__set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_PiecewiseIsometry_mk__of__set(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_inc(x_12);
return x_12;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PiecewiseIsometry_mk__two__pieces___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_mk__two__pieces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_PiecewiseIsometry_mk__two__pieces(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PiecewiseIsometry_of__isometry___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_of__isometry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PiecewiseIsometry_of__isometry(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_PiecewiseIsometry_id___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_id(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PiecewiseIsometry_id___closed__0;
return x_5;
}
}
LEAN_EXPORT lean_object* l_PiecewiseIsometry_id___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PiecewiseIsometry_id(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_MetricSpace_Isometry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Constructions_BorelSpace_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TDCSG_Properties(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Isometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Constructions_BorelSpace_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PiecewiseIsometry_id___closed__0 = _init_l_PiecewiseIsometry_id___closed__0();
lean_mark_persistent(l_PiecewiseIsometry_id___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
