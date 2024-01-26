forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && (a::"" in ((context == context) == (principal == context)))
};
