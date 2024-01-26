permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (([true, false] in action) in action)) && true
};
