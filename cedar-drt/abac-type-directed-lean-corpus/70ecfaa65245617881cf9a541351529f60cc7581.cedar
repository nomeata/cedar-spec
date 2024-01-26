permit(
  principal is a in a::"6666\0&6",
  action in [Action::"action"],
  resource is a in a::"6666\0&6"
) when {
  true && (!(!(action is a)))
};
