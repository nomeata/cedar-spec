permit(
  principal is a,
  action == Action::"action",
  resource == a::"mpl"
) when {
  true && ((Ahhc0::"tmpl" in action).isInRange(action))
};
