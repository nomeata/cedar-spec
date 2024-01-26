@r("\u{6}")
forbid(
  principal is x::a in x::a::"",
  action in [x::Action::"action",x::Action::"action",x::Action::"action"],
  resource == x::a::"\0\0\0\0\01\0\0\0\0\0\0\0\0\0\u{18}\0\0"
) when {
  true
};
