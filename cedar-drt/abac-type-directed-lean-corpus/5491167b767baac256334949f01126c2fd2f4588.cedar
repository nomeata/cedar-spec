permit(
  principal in a::"\u{2}\0pppppppppppppppppppppppp",
  action == Action::"action",
  resource is a in a::"\u{2}\0pppppppppppppppppppppppp"
) when {
  true
};
