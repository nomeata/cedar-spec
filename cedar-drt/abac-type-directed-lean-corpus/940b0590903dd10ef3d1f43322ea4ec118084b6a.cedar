permit(
  principal is a in a::"",
  action in [Action::"action",Action::"action"],
  resource is a in a::"6"
) when {
  true && ([].containsAll(if (resource in principal) then [false, false] else [false, false, true]))
};
