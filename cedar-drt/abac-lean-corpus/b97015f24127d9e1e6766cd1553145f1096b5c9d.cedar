@r("\u{1}\0")
permit(
  principal,
  action,
  resource
) when {
  true && (((resource in action) == r3310O00N03::"ief") == ((action in principal) == principal))
};
