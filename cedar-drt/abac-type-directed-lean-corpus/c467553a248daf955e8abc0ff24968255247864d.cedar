forbid(
  principal,
  action,
  resource == r::r::r::r::a::""
) when {
  true && (action has "")
};
