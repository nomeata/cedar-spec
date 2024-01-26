forbid(
  principal == a::"",
  action in [Action::":"],
  resource == a::""
) when {
  (true && ((if (principal has "") then resource else a::"") in a::"")) && true
};
