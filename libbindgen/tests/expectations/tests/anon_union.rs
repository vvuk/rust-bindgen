/* automatically generated by rust-bindgen */


#![allow(non_snake_case)]


#[repr(C)]
pub struct __BindgenUnionField<T>(::std::marker::PhantomData<T>);
impl <T> __BindgenUnionField<T> {
    #[inline]
    pub fn new() -> Self { __BindgenUnionField(::std::marker::PhantomData) }
    #[inline]
    pub unsafe fn as_ref(&self) -> &T { ::std::mem::transmute(self) }
    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut T { ::std::mem::transmute(self) }
}
impl <T> ::std::default::Default for __BindgenUnionField<T> {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl <T> ::std::clone::Clone for __BindgenUnionField<T> {
    #[inline]
    fn clone(&self) -> Self { Self::new() }
}
impl <T> ::std::marker::Copy for __BindgenUnionField<T> { }
impl <T> ::std::fmt::Debug for __BindgenUnionField<T> {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        fmt.write_str("__BindgenUnionField")
    }
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct TErrorResult<T> {
    pub mResult: ::std::os::raw::c_int,
    pub __bindgen_anon_1: TErrorResult__bindgen_ty_1<T>,
    pub mMightHaveUnreported: bool,
    pub mUnionState: TErrorResult_UnionState,
    pub _phantom_0: ::std::marker::PhantomData<T>,
}
pub const TErrorResult_UnionState_HasException: TErrorResult_UnionState =
    TErrorResult_UnionState::HasMessage;
#[repr(i32)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TErrorResult_UnionState { HasMessage = 0, }
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct TErrorResult_Message<T> {
    pub _address: u8,
    pub _phantom_0: ::std::marker::PhantomData<T>,
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct TErrorResult_DOMExceptionInfo<T> {
    pub _address: u8,
    pub _phantom_0: ::std::marker::PhantomData<T>,
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct TErrorResult__bindgen_ty_1<T> {
    pub mMessage: __BindgenUnionField<*mut TErrorResult_Message<T>>,
    pub mDOMExceptionInfo: __BindgenUnionField<*mut TErrorResult_DOMExceptionInfo<T>>,
    pub bindgen_union_field: u64,
    pub _phantom_0: ::std::marker::PhantomData<T>,
}
#[test]
fn __bindgen_test_layout_template_17() {
    assert_eq!(::std::mem::size_of::<TErrorResult<::std::os::raw::c_int>>() ,
               24usize);
    assert_eq!(::std::mem::align_of::<TErrorResult<::std::os::raw::c_int>>() ,
               8usize);
}
#[repr(C)]
#[derive(Debug, Copy)]
pub struct ErrorResult {
    pub _base: TErrorResult<::std::os::raw::c_int>,
}
#[test]
fn bindgen_test_layout_ErrorResult() {
    assert_eq!(::std::mem::size_of::<ErrorResult>() , 24usize);
    assert_eq!(::std::mem::align_of::<ErrorResult>() , 8usize);
}
impl Clone for ErrorResult {
    fn clone(&self) -> Self { *self }
}
