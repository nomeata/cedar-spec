forbid(
  principal is B::a in B::a::"",
  action in [B::Action::"action"],
  resource == B::a::""
) when {
  (true && (B::a::"" is B::a)) && false
};
