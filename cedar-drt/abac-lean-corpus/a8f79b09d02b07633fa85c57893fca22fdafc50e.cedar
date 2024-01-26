permit(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource
) when {
  (true && ({"A01hh": false in principal, "A": principal}[""])) && principal
};
