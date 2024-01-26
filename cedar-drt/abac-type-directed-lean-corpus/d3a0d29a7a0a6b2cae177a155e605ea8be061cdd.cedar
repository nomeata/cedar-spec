permit(
  principal is a in a::"7",
  action in [Action::"action"],
  resource is a in a::"7"
) when {
  (true && (!(!(action is a)))) && ((ip("128.9.255.153")) == (ip("0.0.0.0")))
};
