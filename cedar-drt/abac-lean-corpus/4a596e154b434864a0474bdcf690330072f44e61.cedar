permit(
  principal == a::"j",
  action in [Action::"action"],
  resource
) when {
  true && (a::"" has "on_train")
};
