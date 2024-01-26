@B("")
forbid(
  principal,
  action,
  resource
) when {
  (true && (a::"" in principal)) && (if ((ip("0.54.203.204")) == (decimal("0.0"))) then false else false)
};
