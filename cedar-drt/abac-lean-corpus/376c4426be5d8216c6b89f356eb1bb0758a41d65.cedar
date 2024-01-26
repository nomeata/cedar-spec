forbid(
  principal == a::"\u{b}\u{2}",
  action,
  resource == a::"\u{b}\u{2}"
) when {
  true && ({"Aw0hh": !false} == (Action::"action" == principal))
};
