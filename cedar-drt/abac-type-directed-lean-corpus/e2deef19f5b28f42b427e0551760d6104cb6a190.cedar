permit(
  principal == a::"6",
  action == Action::"action",
  resource == a::"6"
) when {
  true && ([action in action].containsAll(if ((ip("6767:6767:e500:ff:6e:6f69:7369:6365/033")).isMulticast()) then [] else []))
};
