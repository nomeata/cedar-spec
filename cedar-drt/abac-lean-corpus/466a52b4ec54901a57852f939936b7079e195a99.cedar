permit(
  principal,
  action in [Action::"h",Action::"",Action::"j;jj"],
  resource
) when {
  true && [!((principal["\t\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"]) <= principal), principal]
};
