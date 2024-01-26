permit(
  principal == a::"",
  action,
  resource
) when {
  true && ([a::"", Action::"action", a::""].contains(a::"\0\0\u{13}\0\0"))
};
