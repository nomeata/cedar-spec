forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (action in principal)) && (principal is a)) && ((if false then [false, false] else (if false then [] else [])).contains(false))
};
