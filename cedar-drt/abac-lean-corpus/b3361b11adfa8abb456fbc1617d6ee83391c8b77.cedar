forbid(
  principal is a in a::"jj\0",
  action in [Action::"action"],
  resource == a::"jj\0"
) when {
  (true && (((principal in principal) in "") in (!principal))) && action
};
