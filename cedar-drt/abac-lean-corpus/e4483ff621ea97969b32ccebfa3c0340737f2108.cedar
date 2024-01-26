@Mlb0233("")
forbid(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"\u{10}\0"
) when {
  false && principal
};
