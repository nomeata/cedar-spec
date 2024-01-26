permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && [true, !false, a::"jbjjj" in (a::"" == true)]
};
