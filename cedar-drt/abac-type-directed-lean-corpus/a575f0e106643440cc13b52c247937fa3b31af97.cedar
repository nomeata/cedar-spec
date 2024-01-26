permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource
) when {
  ((true && (action in action)) && true) && true
};
