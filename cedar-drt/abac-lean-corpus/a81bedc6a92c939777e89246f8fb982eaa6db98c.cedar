forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (((context in a::"") in principal) in principal)) && ""
};
