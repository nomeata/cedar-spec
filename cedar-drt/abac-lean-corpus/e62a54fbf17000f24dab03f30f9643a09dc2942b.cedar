forbid(
  principal == a::"",
  action in [Action::"",Action::"",Action::""],
  resource in a::"\u{6}"
) when {
  ((true && (((a::"\u{6}" == a::"\u{6}") == (a::"\u{6}" == a::"\u{6}")) == ((a::"\u{6}" == a::"\u{6}") == (a::"\u{6}" == a::"\u{6}")))) && (((a::"\u{6}" == a::"\u{6}") == (a::"\u{6}" == a::"\u{6}")) == ((a::"\u{6}" == a::"\u{6}") == (a::"\u{6}" == a::"\u{6}")))) && (false == principal)
};
