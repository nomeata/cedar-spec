forbid(
  principal is a in a::"",
  action in [Action::"++++++++++++++++++++"],
  resource is a in a::""
) when {
  ((true && (action in [action])) && (a::"" in (if (resource in []) then [principal] else [principal]))) && ((a::"" in [principal, principal]) && false)
};
