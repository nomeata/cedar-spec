@A("")
@r("\0\0")
forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true
};
