@Ah13301("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ("".contains(a::""))
};
