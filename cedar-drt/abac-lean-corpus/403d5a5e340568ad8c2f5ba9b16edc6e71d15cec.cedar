permit(
  principal == a::"j",
  action in [Action::""],
  resource is a in a::"j"
) when {
  true && (!((!(false <= principal)) < principal))
};
