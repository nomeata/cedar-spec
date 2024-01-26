permit(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::"\u{16}6\u{16}6@"
) when {
  true && ((if (principal is a) then [] else [[], [], []]).containsAny([{}]))
};
