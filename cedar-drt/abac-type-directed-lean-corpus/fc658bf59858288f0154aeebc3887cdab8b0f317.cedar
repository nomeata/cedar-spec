permit(
  principal,
  action in [Action::"action"],
  resource == a::"\u{1d}\u{1d}\u{1d}"
) when {
  true && ((if (action in resource) then (if false then "" else "") else (if false then "" else "")) == "")
};
