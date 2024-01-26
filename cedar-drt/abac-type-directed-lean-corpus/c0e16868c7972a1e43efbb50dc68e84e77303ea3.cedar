permit(
  principal == a::"",
  action,
  resource
) when {
  true && ([a::"", resource, principal].contains(a::"\0\0\u{13}\0\0"))
};
