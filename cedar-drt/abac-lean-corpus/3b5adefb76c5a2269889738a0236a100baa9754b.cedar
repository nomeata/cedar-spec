permit(
  principal in a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (((-(false)).contains(action)) == action)) && false
};
