permit(
  principal == a::"",
  action,
  resource
) when {
  true && ([a::"", Action::"action", action].contains(a::"\0\0\0\0y\0\0\u{13}\0\0"))
};
