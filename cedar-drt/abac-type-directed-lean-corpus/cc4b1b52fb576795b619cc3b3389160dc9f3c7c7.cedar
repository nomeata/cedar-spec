permit(
  principal is a in a::"",
  action,
  resource == a::""
) when {
  true && ([a::"u\0\0", Action::"action", a::""].contains(a::""))
};
